import MidenLean.Proofs.Tactics
import MidenLean.Generated.Sha256

namespace MidenLean.Proofs.Sha256

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `sha256::cap_sigma_0` computes the SHA-256 Σ₀ function: ROTR(a,2) ⊕ ROTR(a,13) ⊕ ROTR(a,22).
    Input stack:  [a] ++ rest
    Output stack: [ROTR(a,2) ⊕ (ROTR(a,13) ⊕ ROTR(a,22))] ++ rest -/
theorem sha256_cap_sigma_0_correct
    (a : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: rest)
    (ha : a.isU32 = true) :
    exec 14 s Miden.Core.Sha256.cap_sigma_0 =
    some (s.withStack (
      Felt.ofNat (u32RotateRight a.val 2 ^^^
        (u32RotateRight a.val 13 ^^^ u32RotateRight a.val 22)) :: rest)) := by
  miden_setup Miden.Core.Sha256.cap_sigma_0
  have ha_lt : a.val < 2^32 := by simpa [Felt.isU32] using ha
  have hr2_u32  : (Felt.ofNat (u32RotateRight a.val 2)).isU32  = true :=
    u32RotateRight_isU32 a ha 2
  have hr13_u32 : (Felt.ofNat (u32RotateRight a.val 13)).isU32 = true :=
    u32RotateRight_isU32 a ha 13
  have hr22_u32 : (Felt.ofNat (u32RotateRight a.val 22)).isU32 = true :=
    u32RotateRight_isU32 a ha 22
  have hr2_val  : (Felt.ofNat (u32RotateRight a.val 2)).val  = u32RotateRight a.val 2 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 2 ha_lt)
  have hr13_val : (Felt.ofNat (u32RotateRight a.val 13)).val = u32RotateRight a.val 13 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 13 ha_lt)
  have hr22_val : (Felt.ofNat (u32RotateRight a.val 22)).val = u32RotateRight a.val 22 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 22 ha_lt)
  have hx_lt : u32RotateRight a.val 13 ^^^ u32RotateRight a.val 22 < 2^32 :=
    Nat.bitwise_lt_two_pow (u32RotateRight_lt a.val 13 ha_lt) (u32RotateRight_lt a.val 22 ha_lt)
  have hx_u32 : (Felt.ofNat (u32RotateRight a.val 13 ^^^ u32RotateRight a.val 22)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hx_lt
  have hx_val : (Felt.ofNat (u32RotateRight a.val 13 ^^^ u32RotateRight a.val 22)).val =
      u32RotateRight a.val 13 ^^^ u32RotateRight a.val 22 :=
    felt_ofNat_val_of_u32 _ hx_lt
  -- Instruction 1: dup 0
  miden_dup
  -- Instruction 2: u32RotrImm 2
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  -- Instruction 3: swap 1
  miden_swap
  -- Instruction 4: dup 0
  miden_dup
  -- Instruction 5: u32RotrImm 13
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  -- Instruction 6: swap 1
  miden_swap
  -- Instruction 7: u32RotrImm 22
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  -- Instruction 8: u32Xor (top = ROTR(a,22), second = ROTR(a,13))
  rw [stepU32Xor (ha := hr13_u32) (hb := hr22_u32)]; miden_bind
  rw [hr13_val, hr22_val]
  -- Instruction 9: u32Xor (top = ROTR13^^^ROTR22, second = ROTR(a,2))
  rw [stepU32Xor (ha := hr2_u32) (hb := hx_u32)]; miden_bind
  rw [hr2_val, hx_val]
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs.Sha256
