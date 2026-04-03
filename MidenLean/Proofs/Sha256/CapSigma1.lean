import MidenLean.Proofs.Tactics
import MidenLean.Generated.Sha256

namespace MidenLean.Proofs.Sha256

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `sha256::cap_sigma_1` computes the SHA-256 Σ₁ function: ROTR(a,6) ⊕ ROTR(a,11) ⊕ ROTR(a,25).
    Input stack:  [a] ++ rest
    Output stack: [ROTR(a,6) ⊕ (ROTR(a,11) ⊕ ROTR(a,25))] ++ rest -/
theorem sha256_cap_sigma_1_correct
    (a : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: rest)
    (ha : a.isU32 = true) :
    exec 14 s Miden.Core.Sha256.cap_sigma_1 =
    some (s.withStack (
      Felt.ofNat (u32RotateRight a.val 6 ^^^
        (u32RotateRight a.val 11 ^^^ u32RotateRight a.val 25)) :: rest)) := by
  miden_setup Miden.Core.Sha256.cap_sigma_1
  have ha_lt : a.val < 2^32 := by simpa [Felt.isU32] using ha
  have hr6_u32  : (Felt.ofNat (u32RotateRight a.val 6)).isU32  = true :=
    u32RotateRight_isU32 a ha 6
  have hr11_u32 : (Felt.ofNat (u32RotateRight a.val 11)).isU32 = true :=
    u32RotateRight_isU32 a ha 11
  have hr25_u32 : (Felt.ofNat (u32RotateRight a.val 25)).isU32 = true :=
    u32RotateRight_isU32 a ha 25
  have hr6_val  : (Felt.ofNat (u32RotateRight a.val 6)).val  = u32RotateRight a.val 6 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 6 ha_lt)
  have hr11_val : (Felt.ofNat (u32RotateRight a.val 11)).val = u32RotateRight a.val 11 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 11 ha_lt)
  have hr25_val : (Felt.ofNat (u32RotateRight a.val 25)).val = u32RotateRight a.val 25 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 25 ha_lt)
  have hx_lt : u32RotateRight a.val 11 ^^^ u32RotateRight a.val 25 < 2^32 :=
    Nat.bitwise_lt_two_pow (u32RotateRight_lt a.val 11 ha_lt) (u32RotateRight_lt a.val 25 ha_lt)
  have hx_u32 : (Felt.ofNat (u32RotateRight a.val 11 ^^^ u32RotateRight a.val 25)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hx_lt
  have hx_val : (Felt.ofNat (u32RotateRight a.val 11 ^^^ u32RotateRight a.val 25)).val =
      u32RotateRight a.val 11 ^^^ u32RotateRight a.val 25 :=
    felt_ofNat_val_of_u32 _ hx_lt
  -- Instruction 1: dup 0
  miden_dup
  -- Instruction 2: u32RotrImm 6
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  -- Instruction 3: swap 1
  miden_swap
  -- Instruction 4: dup 0
  miden_dup
  -- Instruction 5: u32RotrImm 11
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  -- Instruction 6: swap 1
  miden_swap
  -- Instruction 7: u32RotrImm 25
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  -- Instruction 8: u32Xor (top = ROTR(a,25), second = ROTR(a,11))
  rw [stepU32Xor (ha := hr11_u32) (hb := hr25_u32)]; miden_bind
  rw [hr11_val, hr25_val]
  -- Instruction 9: u32Xor (top = ROTR11^^^ROTR25, second = ROTR(a,6))
  rw [stepU32Xor (ha := hr6_u32) (hb := hx_u32)]; miden_bind
  rw [hr6_val, hx_val]
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs.Sha256
