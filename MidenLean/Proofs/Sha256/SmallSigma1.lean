import MidenLean.Proofs.Tactics
import MidenLean.Generated.Sha256

namespace MidenLean.Proofs.Sha256

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `sha256::small_sigma_1` computes the SHA-256 σ₁ function: ROTR(a,17) ⊕ ROTR(a,19) ⊕ SHR(a,10).
    Input stack:  [a] ++ rest
    Output stack: [ROTR(a,17) ⊕ (ROTR(a,19) ⊕ SHR(a,10))] ++ rest -/
theorem sha256_small_sigma_1_correct
    (a : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: rest)
    (ha : a.isU32 = true) :
    exec 14 s Miden.Core.Sha256.small_sigma_1 =
    some (s.withStack (
      Felt.ofNat (u32RotateRight a.val 17 ^^^
        (u32RotateRight a.val 19 ^^^ a.val / 2^10)) :: rest)) := by
  miden_setup Miden.Core.Sha256.small_sigma_1
  -- u32 bounds for intermediate values
  have ha_lt : a.val < 2^32 := by simpa [Felt.isU32] using ha
  have hr17_u32 : (Felt.ofNat (u32RotateRight a.val 17)).isU32 = true :=
    u32RotateRight_isU32 a ha 17
  have hr19_u32 : (Felt.ofNat (u32RotateRight a.val 19)).isU32 = true :=
    u32RotateRight_isU32 a ha 19
  have hs10_u32 : (Felt.ofNat (a.val / 2^10)).isU32 = true :=
    u32Shr_isU32 a ha 10
  -- .val recovery for intermediate Felt.ofNat values
  have hr17_val : (Felt.ofNat (u32RotateRight a.val 17)).val = u32RotateRight a.val 17 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 17 ha_lt)
  have hr19_val : (Felt.ofNat (u32RotateRight a.val 19)).val = u32RotateRight a.val 19 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 19 ha_lt)
  have hs10_val : (Felt.ofNat (a.val / 2^10)).val = a.val / 2^10 :=
    felt_ofNat_val_of_u32 _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha_lt)
  -- u32 bound and .val for the XOR intermediate
  have hx_lt : u32RotateRight a.val 19 ^^^ a.val / 2^10 < 2^32 :=
    Nat.bitwise_lt_two_pow (u32RotateRight_lt a.val 19 ha_lt)
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha_lt)
  have hx_u32 : (Felt.ofNat (u32RotateRight a.val 19 ^^^ a.val / 2^10)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hx_lt
  have hx_val : (Felt.ofNat (u32RotateRight a.val 19 ^^^ a.val / 2^10)).val =
      u32RotateRight a.val 19 ^^^ a.val / 2^10 :=
    felt_ofNat_val_of_u32 _ hx_lt
  -- Instruction 1: dup 0
  miden_dup
  -- Instruction 2: u32RotrImm 17
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  -- Instruction 3: swap 1
  miden_swap
  -- Instruction 4: dup 0
  miden_dup
  -- Instruction 5: u32RotrImm 19
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  -- Instruction 6: swap 1
  miden_swap
  -- Instruction 7: u32ShrImm 10
  rw [stepU32ShrImm (ha := ha) (hn := by decide)]; miden_bind
  -- Instruction 8: u32Xor (top = SHR(a,10), second = ROTR(a,19))
  rw [stepU32Xor (ha := hr19_u32) (hb := hs10_u32)]; miden_bind
  rw [hr19_val, hs10_val]
  -- Instruction 9: u32Xor (top = ROTR19^^^SHR10, second = ROTR(a,17))
  rw [stepU32Xor (ha := hr17_u32) (hb := hx_u32)]; miden_bind
  rw [hr17_val, hx_val]
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs.Sha256
