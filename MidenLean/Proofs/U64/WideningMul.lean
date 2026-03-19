import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

private theorem exec_append (fuel : Nat) (s : MidenState) (xs ys : List Op) :
    exec fuel s (xs ++ ys) = (do
      let s' ← exec fuel s xs
      exec fuel s' ys) := by
  unfold exec execWithEnv
  cases fuel <;> simp [List.foldlM_append]

private def widening_mul_chunk1 : List Op := [
  .inst (.reversew),
  .inst (.dup 3),
  .inst (.dup 2),
  .inst (.u32WidenMul),
  .inst (.swap 1),
  .inst (.dup 4),
  .inst (.movup 4),
  .inst (.u32WidenMadd),
  .inst (.movup 5),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.swap 1)
]

private def widening_mul_chunk2 : List Op := [
  .inst (.movup 5),
  .inst (.movup 5),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 3),
  .inst (.movup 2),
  .inst (.u32WidenAdd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.reversew)
]

private theorem widening_mul_decomp :
    Miden.Core.U64.widening_mul = widening_mul_chunk1 ++ widening_mul_chunk2 := by
  simp [Miden.Core.U64.widening_mul, widening_mul_chunk1, widening_mul_chunk2]

set_option maxHeartbeats 12000000 in
private theorem widening_mul_chunk1_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    exec 30 ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ widening_mul_chunk1 =
      some ⟨Felt.ofNat
              ((b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) /
                2 ^ 32) ::
            Felt.ofNat
              ((b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) %
                2 ^ 32) ::
            Felt.ofNat ((b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) / 2 ^ 32) ::
            Felt.ofNat (b_lo.val * a_lo.val % 2 ^ 32) ::
            a_hi :: b_hi :: rest, mem, locs, adv⟩ := by
  unfold exec widening_mul_chunk1 execWithEnv
  simp only [List.foldlM]
  rw [stepReversew]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WidenMul (ha := hb_lo) (hb := ha_lo)]
  miden_bind
  miden_swap
  miden_dup
  miden_movup
  have h_prod0_hi_isU32 : (Felt.ofNat (b_lo.val * a_lo.val / 2 ^ 32)).isU32 = true :=
    u32_prod_div_isU32 b_lo a_lo hb_lo ha_lo
  rw [stepU32WidenMadd (ha := hb_hi) (hb := ha_lo) (hc := h_prod0_hi_isU32)]
  miden_bind
  have h_prod0_hi_val : (Felt.ofNat (b_lo.val * a_lo.val / 2 ^ 32)).val =
      b_lo.val * a_lo.val / 2 ^ 32 :=
    felt_ofNat_val_lt _ (u32_prod_div_lt_prime b_lo a_lo hb_lo ha_lo)
  rw [h_prod0_hi_val]
  miden_movup
  miden_dup
  have h_cross1_lo_isU32 :
      (Felt.ofNat ((b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32)).isU32 = true :=
    u32_mod_isU32 _
  rw [stepU32WidenMadd (ha := hb_lo) (hb := ha_hi) (hc := h_cross1_lo_isU32)]
  miden_bind
  have h_cross1_lo_val :
      (Felt.ofNat ((b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32)).val =
        (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32 :=
    felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  rw [h_cross1_lo_val]
  miden_swap
  simp only [pure, Pure.pure]

set_option maxHeartbeats 12000000 in
private theorem widening_mul_chunk2_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    exec 30
        ⟨Felt.ofNat
            ((b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) /
              2 ^ 32) ::
          Felt.ofNat
            ((b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) %
              2 ^ 32) ::
          Felt.ofNat ((b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) / 2 ^ 32) ::
          Felt.ofNat (b_lo.val * a_lo.val % 2 ^ 32) ::
          a_hi :: b_hi :: rest, mem, locs, adv⟩
        widening_mul_chunk2 =
      some ⟨Felt.ofNat (b_lo.val * a_lo.val % 2 ^ 32) ::
            Felt.ofNat
              ((b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) %
                2 ^ 32) ::
            Felt.ofNat
              ((((b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) / 2 ^ 32) +
                  (b_hi.val * a_hi.val +
                    (b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) /
                      2 ^ 32) %
                    2 ^ 32) %
                  2 ^ 32) ::
            (Felt.ofNat
                ((((b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) / 2 ^ 32) +
                    (b_hi.val * a_hi.val +
                      (b_lo.val * a_hi.val +
                          (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) /
                        2 ^ 32) %
                      2 ^ 32) /
                  2 ^ 32) +
              Felt.ofNat
                ((b_hi.val * a_hi.val +
                    (b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) /
                      2 ^ 32) /
                  2 ^ 32)) ::
            rest, mem, locs, adv⟩ := by
  unfold exec widening_mul_chunk2 execWithEnv
  simp only [List.foldlM]
  miden_movup
  miden_movup
  have h_cross2_hi_isU32 :
      (Felt.ofNat
        ((b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) /
          2 ^ 32)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    simp only [Felt.isU32, decide_eq_true_eq] at ha_lo ha_hi hb_lo hb_hi
    have htotal :
        b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32 ≤
          (2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1) :=
      Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    calc
      (b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) / 2 ^ 32 ≤
          ((2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := Nat.div_le_div_right htotal
      _ < 2 ^ 32 := by native_decide
  rw [stepU32WidenMadd (ha := hb_hi) (hb := ha_hi) (hc := h_cross2_hi_isU32)]
  miden_bind
  have h_cross2_hi_val :
      (Felt.ofNat
        ((b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) /
          2 ^ 32)).val =
        (b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) /
          2 ^ 32 := by
    apply felt_ofNat_val_lt
    simp only [Felt.isU32, decide_eq_true_eq] at ha_lo ha_hi hb_lo hb_hi
    have htotal :
        b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32 ≤
          (2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1) :=
      Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    calc
      (b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) / 2 ^ 32 ≤
          ((2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := Nat.div_le_div_right htotal
      _ < GOLDILOCKS_PRIME := by
        unfold GOLDILOCKS_PRIME
        native_decide
  rw [h_cross2_hi_val]
  miden_swap
  miden_movup
  miden_movup
  have h_cross1_hi_isU32 :
      (Felt.ofNat ((b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) / 2 ^ 32)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    simp only [Felt.isU32, decide_eq_true_eq] at ha_lo hb_lo hb_hi
    have htotal : b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32 ≤
        (2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1) :=
      Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (by
        have : b_lo.val * a_lo.val ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        calc
          b_lo.val * a_lo.val / 2 ^ 32 ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) / 2 ^ 32 := Nat.div_le_div_right this
          _ ≤ 2 ^ 32 - 1 := by native_decide)
    calc
      (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) / 2 ^ 32 ≤
          ((2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := Nat.div_le_div_right htotal
      _ < 2 ^ 32 := by native_decide
  have h_cross1_hi_val :
      (Felt.ofNat ((b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) / 2 ^ 32)).val =
        (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) / 2 ^ 32 := by
    apply felt_ofNat_val_lt
    simp only [Felt.isU32, decide_eq_true_eq] at ha_lo hb_lo hb_hi
    have htotal : b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32 ≤
        (2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1) :=
      Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (by
        have : b_lo.val * a_lo.val ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        calc
          b_lo.val * a_lo.val / 2 ^ 32 ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) / 2 ^ 32 := Nat.div_le_div_right this
          _ ≤ 2 ^ 32 - 1 := by native_decide)
    calc
      (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) / 2 ^ 32 ≤
          ((2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := Nat.div_le_div_right htotal
      _ < GOLDILOCKS_PRIME := by
        unfold GOLDILOCKS_PRIME
        native_decide
  have h_high_lo_val :
      (Felt.ofNat
        ((b_hi.val * a_hi.val +
            (b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) /
              2 ^ 32) %
          2 ^ 32)).val =
        (b_hi.val * a_hi.val +
            (b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) /
              2 ^ 32) %
          2 ^ 32 :=
    felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  have h_high_lo_isU32 :
      (Felt.ofNat
        ((b_hi.val * a_hi.val +
            (b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) /
              2 ^ 32) %
          2 ^ 32)).isU32 = true :=
    u32_mod_isU32 _
  rw [stepU32WidenAdd (ha := h_cross1_hi_isU32) (hb := h_high_lo_isU32)]
  miden_bind
  rw [h_cross1_hi_val, h_high_lo_val]
  miden_swap
  miden_movup
  rw [stepAdd]
  miden_bind
  rw [stepReversew]
  simp only [pure, Pure.pure]

set_option maxHeartbeats 12000000 in
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
      let cross1 := b_hi.val * a_lo.val + prod0 / 2 ^ 32
      let cross2 := b_lo.val * a_hi.val + cross1 % 2 ^ 32
      let high := b_hi.val * a_hi.val + cross2 / 2 ^ 32
      let widenAdd := cross1 / 2 ^ 32 + high % 2 ^ 32
      Felt.ofNat (prod0 % 2 ^ 32) ::
      Felt.ofNat (cross2 % 2 ^ 32) ::
      Felt.ofNat (widenAdd % 2 ^ 32) ::
      (Felt.ofNat (widenAdd / 2 ^ 32) + Felt.ofNat (high / 2 ^ 32)) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  rw [widening_mul_decomp, exec_append]
  rw [widening_mul_chunk1_correct a_lo a_hi b_lo b_hi rest mem locs adv ha_lo ha_hi hb_lo hb_hi]
  miden_bind
  let prod0 := b_lo.val * a_lo.val
  let cross1 := b_hi.val * a_lo.val + prod0 / 2 ^ 32
  let cross2 := b_lo.val * a_hi.val + cross1 % 2 ^ 32
  let high := b_hi.val * a_hi.val + cross2 / 2 ^ 32
  let widenAdd := cross1 / 2 ^ 32 + high % 2 ^ 32
  simpa [prod0, cross1, cross2, high, widenAdd] using
    (widening_mul_chunk2_correct a_lo a_hi b_lo b_hi rest mem locs adv ha_lo ha_hi hb_lo hb_hi)

end MidenLean.Proofs
