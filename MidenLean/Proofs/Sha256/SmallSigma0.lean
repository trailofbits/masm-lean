import MidenLean.Proofs.Tactics
import MidenLean.Generated.Sha256

namespace MidenLean.Proofs.Sha256

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `sha256::small_sigma_0` computes the SHA-256 σ₀ function: ROTR(a,7) ⊕ ROTR(a,18) ⊕ SHR(a,3).
    Input stack:  [a] ++ rest
    Output stack: [ROTR(a,7) ⊕ (ROTR(a,18) ⊕ SHR(a,3))] ++ rest -/
theorem sha256_small_sigma_0_correct
    (a : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: rest)
    (ha : a.isU32 = true) :
    exec 14 s Miden.Core.Sha256.small_sigma_0 =
    some (s.withStack (
      Felt.ofNat (u32RotateRight a.val 7 ^^^
        (u32RotateRight a.val 18 ^^^ a.val / 2^3)) :: rest)) := by
  miden_setup Miden.Core.Sha256.small_sigma_0
  -- u32 bounds for intermediate values
  have ha_lt : a.val < 2^32 := by simpa [Felt.isU32] using ha
  have hr7_u32  : (Felt.ofNat (u32RotateRight a.val 7)).isU32  = true :=
    u32RotateRight_isU32 a ha 7
  have hr18_u32 : (Felt.ofNat (u32RotateRight a.val 18)).isU32 = true :=
    u32RotateRight_isU32 a ha 18
  have hs3_u32  : (Felt.ofNat (a.val / 2^3)).isU32             = true :=
    u32Shr_isU32 a ha 3
  -- .val recovery for intermediate Felt.ofNat values
  have hr7_val  : (Felt.ofNat (u32RotateRight a.val 7)).val  = u32RotateRight a.val 7 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 7 ha_lt)
  have hr18_val : (Felt.ofNat (u32RotateRight a.val 18)).val = u32RotateRight a.val 18 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 18 ha_lt)
  have hs3_val  : (Felt.ofNat (a.val / 2^3)).val = a.val / 2^3 :=
    felt_ofNat_val_of_u32 _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha_lt)
  -- u32 bound and .val for the XOR intermediate
  have hx_lt : u32RotateRight a.val 18 ^^^ a.val / 2^3 < 2^32 :=
    Nat.bitwise_lt_two_pow (u32RotateRight_lt a.val 18 ha_lt)
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha_lt)
  have hx_u32 : (Felt.ofNat (u32RotateRight a.val 18 ^^^ a.val / 2^3)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hx_lt
  have hx_val : (Felt.ofNat (u32RotateRight a.val 18 ^^^ a.val / 2^3)).val =
      u32RotateRight a.val 18 ^^^ a.val / 2^3 :=
    felt_ofNat_val_of_u32 _ hx_lt
  -- Instruction 1: dup 0
  miden_dup
  -- Instruction 2: u32RotrImm 7
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  -- Instruction 3: swap 1
  miden_swap
  -- Instruction 4: dup 0
  miden_dup
  -- Instruction 5: u32RotrImm 18
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  -- Instruction 6: swap 1
  miden_swap
  -- Instruction 7: u32ShrImm 3
  rw [stepU32ShrImm (ha := ha) (hn := by decide)]; miden_bind
  -- Instruction 8: u32Xor (top = SHR(a,3), second = ROTR(a,18))
  rw [stepU32Xor (ha := hr18_u32) (hb := hs3_u32)]; miden_bind
  rw [hr18_val, hs3_val]
  -- Instruction 9: u32Xor (top = ROTR18^^^SHR3, second = ROTR(a,7))
  rw [stepU32Xor (ha := hr7_u32) (hb := hx_u32)]; miden_bind
  rw [hr7_val, hx_val]
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs.Sha256
