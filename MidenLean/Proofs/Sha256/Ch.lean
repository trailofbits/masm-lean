import MidenLean.Proofs.Tactics
import MidenLean.Generated.Sha256

namespace MidenLean.Proofs.Sha256

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `sha256::ch` computes the SHA-256 choice function: (e AND f) XOR (NOT(e) AND g).
    Input stack:  [e, f, g] ++ rest
    Output stack: [(e AND f) XOR (NOT(e) AND g)] ++ rest -/
theorem sha256_ch_correct
    (e f g : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = e :: f :: g :: rest)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) :
    exec 13 s Miden.Core.Sha256.ch =
    some (s.withStack (
      Felt.ofNat ((f.val &&& e.val) ^^^ ((u32Max - 1 - e.val) &&& g.val)) :: rest)) := by
  miden_setup Miden.Core.Sha256.ch
  -- u32 bounds for intermediate values
  have he_lt : e.val < 2^32 := by simpa [Felt.isU32] using he
  have hf_lt : f.val < 2^32 := by simpa [Felt.isU32] using hf
  have hg_lt : g.val < 2^32 := by simpa [Felt.isU32] using hg
  -- AND(f, e) intermediate
  have hef_lt  : f.val &&& e.val < 2^32      := Nat.bitwise_lt_two_pow hf_lt he_lt
  have hef_u32 : (Felt.ofNat (f.val &&& e.val)).isU32 = true := felt_ofNat_isU32_of_lt _ hef_lt
  have hef_val : (Felt.ofNat (f.val &&& e.val)).val = f.val &&& e.val :=
    felt_ofNat_val_of_u32 _ hef_lt
  -- NOT(e) = u32Max - 1 - e.val
  have hnot_lt  : u32Max - 1 - e.val < 2^32      := by unfold u32Max; omega
  have hnot_u32 : (Felt.ofNat (u32Max - 1 - e.val)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hnot_lt
  have hnot_val : (Felt.ofNat (u32Max - 1 - e.val)).val = u32Max - 1 - e.val :=
    felt_ofNat_val_of_u32 _ hnot_lt
  -- AND(NOT(e), g) intermediate
  have hng_lt  : (u32Max - 1 - e.val) &&& g.val < 2^32 :=
    Nat.bitwise_lt_two_pow hnot_lt hg_lt
  have hng_u32 : (Felt.ofNat ((u32Max - 1 - e.val) &&& g.val)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hng_lt
  have hng_val : (Felt.ofNat ((u32Max - 1 - e.val) &&& g.val)).val =
      (u32Max - 1 - e.val) &&& g.val :=
    felt_ofNat_val_of_u32 _ hng_lt
  -- Instruction 1: swap 1  →  [f, e, g, rest]
  miden_swap
  -- Instruction 2: dup 1   →  [e, f, e, g, rest]
  miden_dup
  -- Instruction 3: u32And (b=e top, a=f second)  →  [f&e, e, g, rest]
  rw [stepU32And (ha := hf) (hb := he)]; miden_bind
  -- Instruction 4: swap 1  →  [e, f&e, g, rest]
  miden_swap
  -- Instruction 5: u32Not  →  [NOT(e), f&e, g, rest]
  rw [stepU32Not (ha := he)]; miden_bind
  -- Instruction 6: movup 2 →  [g, NOT(e), f&e, rest]
  miden_movup
  -- Instruction 7: u32And (b=g top, a=NOT(e) second)  →  [NOT(e)&g, f&e, rest]
  rw [stepU32And (ha := hnot_u32) (hb := hg)]; miden_bind
  rw [hnot_val]
  -- Instruction 8: u32Xor (b=NOT(e)&g top, a=f&e second)  →  [(f&e)^(NOT(e)&g), rest]
  rw [stepU32Xor (ha := hef_u32) (hb := hng_u32)]; miden_bind
  rw [hef_val, hng_val]
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs.Sha256
