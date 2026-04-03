import MidenLean.Proofs.Tactics
import MidenLean.Generated.Sha256

namespace MidenLean.Proofs.Sha256

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `sha256::maj` computes the SHA-256 majority function: (a AND b) XOR (a AND c) XOR (b AND c).
    Input stack:  [a, b, c] ++ rest
    Output stack: [(a AND b) XOR ((a AND c) XOR (b AND c))] ++ rest -/
theorem sha256_maj_correct
    (a b c : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: rest)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    exec 16 s Miden.Core.Sha256.maj =
    some (s.withStack (
      Felt.ofNat ((b.val &&& a.val) ^^^
        ((a.val &&& c.val) ^^^ (b.val &&& c.val))) :: rest)) := by
  miden_setup Miden.Core.Sha256.maj
  have ha_lt : a.val < 2^32 := by simpa [Felt.isU32] using ha
  have hb_lt : b.val < 2^32 := by simpa [Felt.isU32] using hb
  have hc_lt : c.val < 2^32 := by simpa [Felt.isU32] using hc
  -- AND(b, a)
  have hab_lt  : b.val &&& a.val < 2^32      := Nat.bitwise_lt_two_pow hb_lt ha_lt
  have hab_u32 : (Felt.ofNat (b.val &&& a.val)).isU32 = true := felt_ofNat_isU32_of_lt _ hab_lt
  have hab_val : (Felt.ofNat (b.val &&& a.val)).val = b.val &&& a.val :=
    felt_ofNat_val_of_u32 _ hab_lt
  -- AND(a, c)
  have hac_lt  : a.val &&& c.val < 2^32      := Nat.bitwise_lt_two_pow ha_lt hc_lt
  have hac_u32 : (Felt.ofNat (a.val &&& c.val)).isU32 = true := felt_ofNat_isU32_of_lt _ hac_lt
  have hac_val : (Felt.ofNat (a.val &&& c.val)).val = a.val &&& c.val :=
    felt_ofNat_val_of_u32 _ hac_lt
  -- AND(b, c)
  have hbc_lt  : b.val &&& c.val < 2^32      := Nat.bitwise_lt_two_pow hb_lt hc_lt
  have hbc_u32 : (Felt.ofNat (b.val &&& c.val)).isU32 = true := felt_ofNat_isU32_of_lt _ hbc_lt
  have hbc_val : (Felt.ofNat (b.val &&& c.val)).val = b.val &&& c.val :=
    felt_ofNat_val_of_u32 _ hbc_lt
  -- XOR(AND(a,c), AND(b,c)) intermediate
  have hx_lt  : (a.val &&& c.val) ^^^ (b.val &&& c.val) < 2^32 :=
    Nat.bitwise_lt_two_pow hac_lt hbc_lt
  have hx_u32 : (Felt.ofNat ((a.val &&& c.val) ^^^ (b.val &&& c.val))).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hx_lt
  have hx_val : (Felt.ofNat ((a.val &&& c.val) ^^^ (b.val &&& c.val))).val =
      (a.val &&& c.val) ^^^ (b.val &&& c.val) :=
    felt_ofNat_val_of_u32 _ hx_lt
  -- Instruction 1: dup 1  →  [b, a, b, c, rest]
  miden_dup
  -- Instruction 2: dup 1  →  [a, b, a, b, c, rest]
  miden_dup
  -- Instruction 3: u32And (b_lemma=a top, a_lemma=b second)  →  [b&a, a, b, c, rest]
  rw [stepU32And (ha := hb) (hb := ha)]; miden_bind
  -- Instruction 4: swap 1  →  [a, b&a, b, c, rest]
  miden_swap
  -- Instruction 5: dup 3  →  [c, a, b&a, b, c, rest]
  miden_dup
  -- Instruction 6: u32And (b_lemma=c top, a_lemma=a second)  →  [a&c, b&a, b, c, rest]
  rw [stepU32And (ha := ha) (hb := hc)]; miden_bind
  -- Instruction 7: movup 2  →  [b, a&c, b&a, c, rest]
  miden_movup
  -- Instruction 8: movup 3  →  [c, b, a&c, b&a, rest]
  miden_movup
  -- Instruction 9: u32And (b_lemma=c top, a_lemma=b second)  →  [b&c, a&c, b&a, rest]
  rw [stepU32And (ha := hb) (hb := hc)]; miden_bind
  -- Instruction 10: u32Xor (b_lemma=b&c top, a_lemma=a&c second)  →  [ac^bc, b&a, rest]
  rw [stepU32Xor (ha := hac_u32) (hb := hbc_u32)]; miden_bind
  rw [hac_val, hbc_val]
  -- Instruction 11: u32Xor (b_lemma=ac^bc top, a_lemma=b&a second)  →  [ba^(ac^bc), rest]
  rw [stepU32Xor (ha := hab_u32) (hb := hx_u32)]; miden_bind
  rw [hab_val, hx_val]
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs.Sha256
