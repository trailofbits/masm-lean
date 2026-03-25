import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- Raw version of `u64::wrapping_mul` with explicit Felt arguments.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [c_lo, c_hi] ++ rest
    where c_lo is the low 32 bits and c_hi the high 32 bits of (a * b) mod 2^64. -/
theorem u64_wrapping_mul_raw
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    exec 20 s Miden.Core.U64.wrapping_mul =
    some (s.withStack (
      let prod_lo := a_lo.val * b_lo.val
      let cross1 := b_hi.val * a_lo.val + prod_lo / 2^32
      let cross2 := b_lo.val * a_hi.val + cross1 % 2^32
      Felt.ofNat (prod_lo % 2^32) :: Felt.ofNat (cross2 % 2^32) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.wrapping_mul execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ (.dup 2)
    let s' ← execInstruction s' (.dup 1)
    let s' ← execInstruction s' (.u32WidenMul)
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.movup 3)
    let s' ← execInstruction s' (.movup 4)
    let s' ← execInstruction s' (.u32WidenMadd)
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.drop)
    let s' ← execInstruction s' (.movup 2)
    let s' ← execInstruction s' (.movup 3)
    let s' ← execInstruction s' (.u32WidenMadd)
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.drop)
    let s' ← execInstruction s' (.swap 1)
    pure s') = _
  miden_dup; miden_dup
  rw [stepU32WidenMul (ha := by assumption) (hb := by assumption)]; miden_bind
  miden_swap; miden_movup; miden_movup
  -- u32WidenMadd (b_hi * a_lo + carry)
  have h_carry_val : (Felt.ofNat (a_lo.val * b_lo.val / 2^32)).val =
      a_lo.val * b_lo.val / 2^32 :=
    felt_ofNat_val_lt _ (u32_prod_div_lt_prime a_lo b_lo ha_lo hb_lo)
  have h_prod_lo_isU32 : (Felt.ofNat (a_lo.val * b_lo.val % 2 ^ 32)).isU32 = true :=
    u32_mod_isU32 _
  have h_carry_isU32 : (Felt.ofNat (a_lo.val * b_lo.val / 2 ^ 32)).isU32 = true :=
    u32_prod_div_isU32 a_lo b_lo ha_lo hb_lo
  rw [stepU32WidenMadd (ha := by assumption) (hb := by assumption) (hc := by assumption)]; miden_bind
  rw [h_carry_val]
  miden_swap
  rw [stepDrop]; miden_bind
  miden_movup; miden_movup
  -- u32WidenMadd (b_lo * a_hi + cross1_lo)
  have h_cross1_val : (Felt.ofNat ((b_hi.val * a_lo.val + a_lo.val * b_lo.val / 2^32) % 2^32)).val =
      (b_hi.val * a_lo.val + a_lo.val * b_lo.val / 2^32) % 2^32 :=
    felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  have h_cross1_hi_isU32 : (Felt.ofNat ((b_hi.val * a_lo.val + a_lo.val * b_lo.val / 2 ^ 32) / 2 ^ 32)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    simp only [Felt.isU32, decide_eq_true_eq] at ha_lo hb_lo hb_hi
    have h1 : b_hi.val * a_lo.val ≤ (2^32 - 1) * (2^32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : a_lo.val * b_lo.val / 2^32 ≤ (2^32 - 1) * (2^32 - 1) / 2^32 :=
      Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
    have h3 : (2^32 - 1) * (2^32 - 1) / (2^32 : Nat) = 2^32 - 2 := by native_decide
    have h4 : b_hi.val * a_lo.val + a_lo.val * b_lo.val / 2^32
        ≤ (2^32 - 1) * (2^32 - 1) + (2^32 - 2) := by omega
    have h5 : ((2^32 - 1) * (2^32 - 1) + (2^32 - 2)) / (2^32 : Nat) = 2^32 - 2 := by native_decide
    omega
  have h_cross1_lo_isU32 : (Felt.ofNat ((b_hi.val * a_lo.val + a_lo.val * b_lo.val / 2 ^ 32) % 2 ^ 32)).isU32 = true :=
    u32_mod_isU32 _
  rw [stepU32WidenMadd (ha := by assumption) (hb := by assumption) (hc := by assumption)]; miden_bind
  rw [h_cross1_val]
  miden_swap
  rw [stepDrop]; miden_bind
  miden_swap
  dsimp only [pure, Pure.pure]

/-- `u64::wrapping_mul` computes the low 64 bits of the product `a * b`.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Output stack: [(a * b).lo, (a * b).hi] ++ rest -/
theorem u64_wrapping_mul_correct (a b : U64) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    exec 20 s Miden.Core.U64.wrapping_mul =
    some (s.withStack ((a * b).lo.val :: (a * b).hi.val :: rest)) := by
  rw [u64_wrapping_mul_raw a.lo.val a.hi.val b.lo.val b.hi.val rest s hs a.lo.isU32 a.hi.isU32 b.lo.isU32 b.hi.isU32]
  show _ = some (s.withStack (
    Felt.ofNat ((a.toNat * b.toNat) % 2^32) ::
    Felt.ofNat (((a.toNat * b.toNat) / 2^32) % 2^32) :: rest))
  simp only [U64.toNat]
  congr 1; congr 1; congr 1
  · congr 1; ring_nf; omega
  · congr 1; congr 1; ring_nf; omega

end MidenLean.Proofs
