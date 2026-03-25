import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- Procedure environment for shl that includes wrapping_mul. -/
private def shlProcEnv : ProcEnv := fun name =>
  match name with
  | "wrapping_mul" => some Miden.Core.U64.wrapping_mul
  | _ => none

set_option maxHeartbeats 16000000 in
/-- `u64::shl` raw: result in terms of schoolbook multiplication of limbs. -/
theorem u64_shl_raw
    (lo hi shift : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: lo :: hi :: rest)
    (hshift : shift.val ≤ 63)
    (hlo : lo.isU32 = true)
    (hhi : hi.isU32 = true) :
    let pow := Felt.ofNat (2 ^ shift.val)
    let pow_lo := pow.lo32
    let pow_hi := pow.hi32
    execWithEnv shlProcEnv 20 s Miden.Core.U64.shl =
    some (s.withStack (
      let prod_lo := pow_lo.val * lo.val
      let cross1 := hi.val * pow_lo.val + prod_lo / 2^32
      let cross2 := lo.val * pow_hi.val + cross1 % 2^32
      Felt.ofNat (prod_lo % 2^32) :: Felt.ofNat (cross2 % 2^32) :: rest)) := by
  miden_setup_env Miden.Core.U64.shl
  -- Resolve the wrapping_mul procedure call
  simp only [shlProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  unfold Miden.Core.U64.wrapping_mul execWithEnv
  simp only [List.foldlM, bind, Bind.bind, Option.bind, pure, Pure.pure]
  -- shl preamble: pow2; u32Split; movup 2; movup 3; swap 1
  rw [stepPow2 (ha := by assumption)]; miden_bind
  rw [stepU32Split]; miden_bind
  miden_movup; miden_movup
  miden_swap
  -- wrapping_mul body on [lo, hi, pow_lo, pow_hi | rest]
  -- Establish isU32 for pow_lo
  have h_pow_lo_u32 : (Felt.ofNat (2 ^ shift.val)).lo32.isU32 = true := U32.lo32_isU32 _
  miden_dup; miden_dup
  -- u32WidenMul: pow_lo * lo
  rw [stepU32WidenMul (ha := h_pow_lo_u32) (hb := hlo)]; miden_bind
  miden_swap; miden_movup; miden_movup
  -- u32WidenMadd: hi * pow_lo + carry
  have h_carry_isU32 : (Felt.ofNat ((Felt.ofNat (2 ^ shift.val)).lo32.val * lo.val / 2 ^ 32)).isU32 = true :=
    u32_prod_div_isU32 _ _ h_pow_lo_u32 hlo
  have h_prod_lo_mod_isU32 : (Felt.ofNat ((Felt.ofNat (2 ^ shift.val)).lo32.val * lo.val % 2 ^ 32)).isU32 = true :=
    u32_mod_isU32 _
  rw [stepU32WidenMadd (ha := by assumption) (hb := h_pow_lo_u32) (hc := by assumption)]; miden_bind
  -- Value recovery for the carry
  have h_prod_div : (Felt.ofNat ((Felt.ofNat (2 ^ shift.val)).lo32.val * lo.val / 2^32)).val =
      (Felt.ofNat (2 ^ shift.val)).lo32.val * lo.val / 2^32 :=
    felt_ofNat_val_lt _ (u32_prod_div_lt_prime _ _ h_pow_lo_u32 hlo)
  rw [h_prod_div]
  miden_swap
  rw [stepDrop]; miden_bind
  miden_movup; miden_movup
  -- u32WidenMadd: lo * pow_hi + cross1_lo
  have h_cross1_lo_isU32 : (Felt.ofNat ((hi.val * (Felt.ofNat (2 ^ shift.val)).lo32.val +
      (Felt.ofNat (2 ^ shift.val)).lo32.val * lo.val / 2 ^ 32) % 2 ^ 32)).isU32 = true :=
    u32_mod_isU32 _
  have h_cross1_hi_isU32 : (Felt.ofNat ((hi.val * (Felt.ofNat (2 ^ shift.val)).lo32.val +
      (Felt.ofNat (2 ^ shift.val)).lo32.val * lo.val / 2 ^ 32) / 2 ^ 32)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    simp only [Felt.isU32, decide_eq_true_eq] at h_pow_lo_u32 hlo hhi
    have hcarry_bound : (Felt.ofNat (2 ^ shift.val)).lo32.val * lo.val / 2^32 < 2^32 := by
      have : (Felt.ofNat (2 ^ shift.val)).lo32.val * lo.val ≤ (2^32 - 1) * (2^32 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      calc (Felt.ofNat (2 ^ shift.val)).lo32.val * lo.val / 2^32
          ≤ (2^32 - 1) * (2^32 - 1) / 2^32 := Nat.div_le_div_right this
        _ < 2^32 := by native_decide
    have htotal : hi.val * (Felt.ofNat (2 ^ shift.val)).lo32.val +
        (Felt.ofNat (2 ^ shift.val)).lo32.val * lo.val / 2^32 ≤
        (2^32 - 1) * (2^32 - 1) + (2^32 - 1) :=
      Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    calc (hi.val * (Felt.ofNat (2 ^ shift.val)).lo32.val + (Felt.ofNat (2 ^ shift.val)).lo32.val * lo.val / 2^32) / 2^32
        ≤ ((2^32 - 1) * (2^32 - 1) + (2^32 - 1)) / 2^32 := Nat.div_le_div_right htotal
      _ < 2^32 := by native_decide
  have h_pow_hi_u32 : (Felt.ofNat (2 ^ shift.val)).hi32.isU32 = true := by
    simp only [Felt.hi32, Felt.isU32, decide_eq_true_eq]
    have hpow_val : (Felt.ofNat (2 ^ shift.val)).val = 2 ^ shift.val := by
      apply felt_ofNat_val_lt
      calc 2 ^ shift.val ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) hshift
        _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
    have hdiv_lt_prime : (Felt.ofNat (2 ^ shift.val)).val / 2 ^ 32 < GOLDILOCKS_PRIME := by
      rw [hpow_val]
      calc 2 ^ shift.val / 2 ^ 32 ≤ 2 ^ 63 / 2 ^ 32 :=
        Nat.div_le_div_right (Nat.pow_le_pow_right (by omega) hshift)
        _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
    rw [felt_ofNat_val_lt _ hdiv_lt_prime, hpow_val]
    calc 2 ^ shift.val / 2 ^ 32 ≤ 2 ^ 63 / 2 ^ 32 :=
      Nat.div_le_div_right (Nat.pow_le_pow_right (by omega) hshift)
      _ < 2 ^ 32 := by native_decide
  rw [stepU32WidenMadd (ha := by assumption) (hb := by assumption) (hc := by assumption)]; miden_bind
  -- Value recovery for cross1_lo
  have h_cross1_val : (Felt.ofNat ((hi.val * (Felt.ofNat (2 ^ shift.val)).lo32.val +
      (Felt.ofNat (2 ^ shift.val)).lo32.val * lo.val / 2^32) % 2^32)).val =
      (hi.val * (Felt.ofNat (2 ^ shift.val)).lo32.val +
      (Felt.ofNat (2 ^ shift.val)).lo32.val * lo.val / 2^32) % 2^32 :=
    felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  rw [h_cross1_val]
  miden_swap
  rw [stepDrop]; miden_bind
  miden_swap

/-- `u64::shl` correctly left-shifts a u64 value by `shift` bits.
    Input stack:  [shift, a.lo, a.hi] ++ rest
    Output stack: [(a.shl shift).lo, (a.shl shift).hi] ++ rest -/
theorem u64_shl_correct (a : U64) (shift : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: a.lo.val :: a.hi.val :: rest)
    (hshift : shift.val ≤ 63) :
    execWithEnv shlProcEnv 20 s Miden.Core.U64.shl =
    some (s.withStack ((a.shl shift.val).lo.val :: (a.shl shift.val).hi.val :: rest)) := by
  rw [u64_shl_raw a.lo.val a.hi.val shift rest s hs hshift a.lo.isU32 a.hi.isU32]
  -- Recover lo32/hi32 val to natural numbers
  have hpow_val : (Felt.ofNat (2 ^ shift.val)).val = 2 ^ shift.val :=
    felt_ofNat_val_lt _ (by
      calc 2 ^ shift.val ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) hshift
        _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide)
  have hlo32_val : (Felt.ofNat (2 ^ shift.val)).lo32.val = 2 ^ shift.val % 2^32 := by
    simp only [Felt.lo32]; rw [hpow_val]; exact felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  have hhi32_val : (Felt.ofNat (2 ^ shift.val)).hi32.val = 2 ^ shift.val / 2^32 := by
    simp only [Felt.hi32]; rw [hpow_val]
    exact felt_ofNat_val_lt _ (by
      calc 2 ^ shift.val / 2^32 ≤ 2^63 / 2^32 :=
        Nat.div_le_div_right (Nat.pow_le_pow_right (by omega) hshift)
        _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide)
  -- Bridge to shl definition: show the raw result matches (a.toNat * 2^shift.val)
  dsimp only
  rw [hlo32_val, hhi32_val]
  show _ = some (s.withStack (
    Felt.ofNat ((a.toNat * 2 ^ shift.val) % 2^32) ::
    Felt.ofNat (((a.toNat * 2 ^ shift.val) / 2^32) % 2^32) :: rest))
  simp only [U64.toNat]
  have h_split : 2 ^ shift.val = 2^32 * (2 ^ shift.val / 2^32) + 2 ^ shift.val % 2^32 :=
    (Nat.div_add_mod _ _).symm
  congr 1; congr 1; congr 1
  · congr 1; (conv_rhs => rw [h_split]); ring_nf; omega
  · congr 1; congr 1; (conv_rhs => rw [h_split]); ring_nf; omega

end MidenLean.Proofs
