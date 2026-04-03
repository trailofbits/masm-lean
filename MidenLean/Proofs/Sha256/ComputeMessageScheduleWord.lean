import MidenLean.Proofs.Sha256.Common

namespace MidenLean.Proofs.Sha256

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `sha256::compute_message_schedule_word` computes the SHA-256 message schedule:
    W[i] = σ₁(W[i-2]) + W[i-7] + σ₀(W[i-15]) + W[i-16] (mod 2³²).
    Input stack:  [W[i-2], W[i-7], W[i-15], W[i-16]] ++ rest
    Output stack: [W[i]] ++ rest -/
theorem sha256_compute_message_schedule_word_correct
    (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hc : c.isU32 = true) (hd : d.isU32 = true) :
    execWithEnv sha256ProcEnv 40 s Miden.Core.Sha256.compute_message_schedule_word =
    some (s.withStack (
      let sig1 := u32RotateRight a.val 17 ^^^ (u32RotateRight a.val 19 ^^^ a.val / 2^10)
      let sig0 := u32RotateRight c.val 7 ^^^ (u32RotateRight c.val 18 ^^^ c.val / 2^3)
      Felt.ofNat ((d.val + (b.val + sig1 + sig0) % 2^32) % 2^32) :: rest)) := by
  miden_setup_env Miden.Core.Sha256.compute_message_schedule_word
  -- ===== Instruction 1: exec "small_sigma_1" on a =====
  simp only [sha256ProcEnv]
  miden_call Miden.Core.Sha256.small_sigma_1
  -- σ₁(a) intermediates
  have ha_lt  : a.val < 2^32 := by simpa [Felt.isU32] using ha
  have hr17_u32 : (Felt.ofNat (u32RotateRight a.val 17)).isU32 = true := u32RotateRight_isU32 a ha 17
  have hr19_u32 : (Felt.ofNat (u32RotateRight a.val 19)).isU32 = true := u32RotateRight_isU32 a ha 19
  have hs10_u32 : (Felt.ofNat (a.val / 2^10)).isU32               = true := u32Shr_isU32 a ha 10
  have hr17_val : (Felt.ofNat (u32RotateRight a.val 17)).val = u32RotateRight a.val 17 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 17 ha_lt)
  have hr19_val : (Felt.ofNat (u32RotateRight a.val 19)).val = u32RotateRight a.val 19 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 19 ha_lt)
  have hs10_val : (Felt.ofNat (a.val / 2^10)).val = a.val / 2^10 :=
    felt_ofNat_val_of_u32 _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha_lt)
  have hx1_lt : u32RotateRight a.val 19 ^^^ a.val / 2^10 < 2^32 :=
    Nat.bitwise_lt_two_pow (u32RotateRight_lt a.val 19 ha_lt)
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha_lt)
  have hx1_u32 : (Felt.ofNat (u32RotateRight a.val 19 ^^^ a.val / 2^10)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hx1_lt
  have hx1_val : (Felt.ofNat (u32RotateRight a.val 19 ^^^ a.val / 2^10)).val =
      u32RotateRight a.val 19 ^^^ a.val / 2^10 := felt_ofNat_val_of_u32 _ hx1_lt
  -- σ₁(a) result isU32 and val
  have hsig1_lt : u32RotateRight a.val 17 ^^^ (u32RotateRight a.val 19 ^^^ a.val / 2^10) < 2^32 :=
    Nat.bitwise_lt_two_pow (u32RotateRight_lt a.val 17 ha_lt) hx1_lt
  have hsig1_u32 : (Felt.ofNat (u32RotateRight a.val 17 ^^^
      (u32RotateRight a.val 19 ^^^ a.val / 2^10))).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hsig1_lt
  have hsig1_val : (Felt.ofNat (u32RotateRight a.val 17 ^^^
      (u32RotateRight a.val 19 ^^^ a.val / 2^10))).val =
      u32RotateRight a.val 17 ^^^ (u32RotateRight a.val 19 ^^^ a.val / 2^10) :=
    felt_ofNat_val_of_u32 _ hsig1_lt
  -- Step σ₁(a): dup0, rotr17, swap1, dup0, rotr19, swap1, shr10, xor, xor
  miden_dup
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  miden_swap
  miden_dup
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  miden_swap
  rw [stepU32ShrImm (ha := ha) (hn := by decide)]; miden_bind
  rw [stepU32Xor (ha := hr19_u32) (hb := hs10_u32)]; miden_bind; rw [hr19_val, hs10_val]
  rw [stepU32Xor (ha := hr17_u32) (hb := hx1_u32)]; miden_bind; rw [hr17_val, hx1_val]
  -- ===== Instruction 2: movup 2 (brings c to top) =====
  miden_movup
  -- ===== Instruction 3: exec "small_sigma_0" on c =====
  simp only [sha256ProcEnv]
  unfold Miden.Core.Sha256.small_sigma_0 execWithEnv
  simp only [List.foldlM]
  -- σ₀(c) intermediates
  have hc_lt  : c.val < 2^32 := by simpa [Felt.isU32] using hc
  have hr7c_u32  : (Felt.ofNat (u32RotateRight c.val 7)).isU32  = true := u32RotateRight_isU32 c hc 7
  have hr18c_u32 : (Felt.ofNat (u32RotateRight c.val 18)).isU32 = true := u32RotateRight_isU32 c hc 18
  have hs3c_u32  : (Felt.ofNat (c.val / 2^3)).isU32             = true := u32Shr_isU32 c hc 3
  have hr7c_val  : (Felt.ofNat (u32RotateRight c.val 7)).val  = u32RotateRight c.val 7 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt c.val 7 hc_lt)
  have hr18c_val : (Felt.ofNat (u32RotateRight c.val 18)).val = u32RotateRight c.val 18 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt c.val 18 hc_lt)
  have hs3c_val  : (Felt.ofNat (c.val / 2^3)).val = c.val / 2^3 :=
    felt_ofNat_val_of_u32 _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hc_lt)
  have hx0_lt : u32RotateRight c.val 18 ^^^ c.val / 2^3 < 2^32 :=
    Nat.bitwise_lt_two_pow (u32RotateRight_lt c.val 18 hc_lt)
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hc_lt)
  have hx0_u32 : (Felt.ofNat (u32RotateRight c.val 18 ^^^ c.val / 2^3)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hx0_lt
  have hx0_val : (Felt.ofNat (u32RotateRight c.val 18 ^^^ c.val / 2^3)).val =
      u32RotateRight c.val 18 ^^^ c.val / 2^3 := felt_ofNat_val_of_u32 _ hx0_lt
  -- σ₀(c) result isU32 and val
  have hsig0_lt : u32RotateRight c.val 7 ^^^ (u32RotateRight c.val 18 ^^^ c.val / 2^3) < 2^32 :=
    Nat.bitwise_lt_two_pow (u32RotateRight_lt c.val 7 hc_lt) hx0_lt
  have hsig0_u32 : (Felt.ofNat (u32RotateRight c.val 7 ^^^
      (u32RotateRight c.val 18 ^^^ c.val / 2^3))).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hsig0_lt
  have hsig0_val : (Felt.ofNat (u32RotateRight c.val 7 ^^^
      (u32RotateRight c.val 18 ^^^ c.val / 2^3))).val =
      u32RotateRight c.val 7 ^^^ (u32RotateRight c.val 18 ^^^ c.val / 2^3) :=
    felt_ofNat_val_of_u32 _ hsig0_lt
  -- Step σ₀(c): dup0, rotr7, swap1, dup0, rotr18, swap1, shr3, xor, xor
  miden_dup
  rw [stepU32RotrImm (ha := hc) (hn := by decide)]; miden_bind
  miden_swap
  miden_dup
  rw [stepU32RotrImm (ha := hc) (hn := by decide)]; miden_bind
  miden_swap
  rw [stepU32ShrImm (ha := hc) (hn := by decide)]; miden_bind
  rw [stepU32Xor (ha := hr18c_u32) (hb := hs3c_u32)]; miden_bind; rw [hr18c_val, hs3c_val]
  rw [stepU32Xor (ha := hr7c_u32) (hb := hx0_u32)]; miden_bind; rw [hr7c_val, hx0_val]
  -- ===== Instruction 4: u32WrappingAdd3 (top=σ₀(c), second=σ₁(a), third=b) =====
  -- sum = (b.val + σ₁(a) + σ₀(c)) % 2^32
  rw [stepU32WrappingAdd3 (ha := hb) (hb := hsig1_u32) (hc := hsig0_u32)]; miden_bind
  rw [hsig1_val, hsig0_val]
  -- ===== Instruction 5: u32WrappingAdd (top=sum3, second=d) =====
  have hsum3_u32 : (Felt.ofNat ((b.val +
      (u32RotateRight a.val 17 ^^^ (u32RotateRight a.val 19 ^^^ a.val / 2^10)) +
      (u32RotateRight c.val 7 ^^^ (u32RotateRight c.val 18 ^^^ c.val / 2^3))) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  have hsum3_val : (Felt.ofNat ((b.val +
      (u32RotateRight a.val 17 ^^^ (u32RotateRight a.val 19 ^^^ a.val / 2^10)) +
      (u32RotateRight c.val 7 ^^^ (u32RotateRight c.val 18 ^^^ c.val / 2^3))) % 2^32)).val =
      (b.val + (u32RotateRight a.val 17 ^^^ (u32RotateRight a.val 19 ^^^ a.val / 2^10)) +
      (u32RotateRight c.val 7 ^^^ (u32RotateRight c.val 18 ^^^ c.val / 2^3))) % 2^32 :=
    felt_ofNat_val_of_u32 _ (Nat.mod_lt _ (by norm_num))
  rw [stepU32WrappingAdd (ha := hd) (hb := hsum3_u32)]; miden_bind
  rw [hsum3_val]
  simp only [pure, Pure.pure]

end MidenLean.Proofs.Sha256
