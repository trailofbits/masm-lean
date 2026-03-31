import MidenLean.AIR.SymbolicFrame
set_option maxHeartbeats 8000000
/-! Decoder AIR constraints: 57 base + 0 ext. Auto-extracted. -/

namespace MidenLean.AIR.Constraints.Symbolic.Decoder

open MidenLean MidenLean.AIR

private def base_0_to_19 : List SymbolicConstraint := [
  -- Decoder.base[0]
  fun f => (f.is_first_row * f.colCurr 22),
  -- Decoder.base[1]
  fun f => (f.colCurr 22 * (f.colCurr 22 - 1)),
  -- Decoder.base[2]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28)) * (1 - f.colNext 22))),
  -- Decoder.base[3]
  fun f => (f.is_transition * ((((1 - f.colCurr 9) * f.colCurr 10) * (f.colCurr 11 * f.colCurr 29)) * (1 - f.colNext 22))),
  -- Decoder.base[4]
  fun f => (f.colCurr 7 * (f.colCurr 7 - 1)),
  -- Decoder.base[5]
  fun f => (f.colCurr 8 * (f.colCurr 8 - 1)),
  -- Decoder.base[6]
  fun f => (f.colCurr 9 * (f.colCurr 9 - 1)),
  -- Decoder.base[7]
  fun f => (f.colCurr 10 * (f.colCurr 10 - 1)),
  -- Decoder.base[8]
  fun f => (f.colCurr 11 * (f.colCurr 11 - 1)),
  -- Decoder.base[9]
  fun f => (f.colCurr 12 * (f.colCurr 12 - 1)),
  -- Decoder.base[10]
  fun f => (f.colCurr 13 * (f.colCurr 13 - 1)),
  -- Decoder.base[11]
  fun f => (f.colCurr 28 - ((f.colCurr 13 * (1 - f.colCurr 12)) * f.colCurr 11)),
  -- Decoder.base[12]
  fun f => (f.colCurr 29 - (f.colCurr 13 * f.colCurr 12)),
  -- Decoder.base[13]
  fun f => (((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)) * f.colCurr 7),
  -- Decoder.base[14]
  fun f => ((f.colCurr 13 * f.colCurr 12) * f.colCurr 7),
  -- Decoder.base[15]
  fun f => ((f.colCurr 13 * f.colCurr 12) * f.colCurr 8),
  -- Decoder.base[16]
  fun f => (f.colCurr 25 * (f.colCurr 25 - 1)),
  -- Decoder.base[17]
  fun f => (f.colCurr 26 * (f.colCurr 26 - 1)),
  -- Decoder.base[18]
  fun f => (f.colCurr 27 * (f.colCurr 27 - 1)),
  -- Decoder.base[19]
  fun f => ((((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28)) + (((f.colCurr 7 * (1 - f.colCurr 8)) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28))) * (f.s 0 * (f.s 0 - 1)))
]

private def base_20_to_39 : List SymbolicConstraint := [
  -- Decoder.base[20]
  fun f => (((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * f.h 2),
  -- Decoder.base[21]
  fun f => (((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * f.h 3),
  -- Decoder.base[22]
  fun f => (((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * f.h 4),
  -- Decoder.base[23]
  fun f => (((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * f.h 5),
  -- Decoder.base[24]
  fun f => (((f.colCurr 9 * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) * (1 - f.s 0)),
  -- Decoder.base[25]
  fun f => (((f.colCurr 9 * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) * (1 - f.h 2)),
  -- Decoder.base[26]
  fun f => (((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) * f.h 3) * f.s 0),
  -- Decoder.base[27]
  fun f => (f.is_transition * (((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) * ((f.colNext 9 * (1 - f.colNext 10)) * (f.colNext 11 * f.colNext 29))) * (f.colNext 14 - f.colCurr 14))),
  -- Decoder.base[28]
  fun f => (f.is_transition * (((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) * ((f.colNext 9 * (1 - f.colNext 10)) * (f.colNext 11 * f.colNext 29))) * (f.colNext 15 - f.colCurr 15))),
  -- Decoder.base[29]
  fun f => (f.is_transition * (((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) * ((f.colNext 9 * (1 - f.colNext 10)) * (f.colNext 11 * f.colNext 29))) * (f.h' 0 - f.h 0))),
  -- Decoder.base[30]
  fun f => (f.is_transition * (((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) * ((f.colNext 9 * (1 - f.colNext 10)) * (f.colNext 11 * f.colNext 29))) * (f.h' 1 - f.h 1))),
  -- Decoder.base[31]
  fun f => (f.is_transition * (((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) * ((f.colNext 9 * (1 - f.colNext 10)) * (f.colNext 11 * f.colNext 29))) * (f.h' 2 - f.h 2))),
  -- Decoder.base[32]
  fun f => (f.is_transition * (((f.colCurr 9 * f.colCurr 10) * (f.colCurr 11 * f.colCurr 29)) * (1 - ((f.colNext 9 * f.colNext 10) * (f.colNext 11 * f.colNext 29))))),
  -- Decoder.base[33]
  fun f => (f.is_transition * ((f.colCurr 22 * (f.colCurr 23 - f.colNext 23)) * ((f.colCurr 23 - f.colNext 23) - 1))),
  -- Decoder.base[34]
  fun f => (f.is_transition * (((f.colCurr 22 * (f.colCurr 23 - f.colNext 23)) * (1 - (((f.colCurr 7 * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)))) * f.colCurr 14)),
  -- Decoder.base[35]
  fun f => (f.is_transition * (((((((1 - f.colCurr 7) * f.colCurr 8) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28)) + (((1 - f.colCurr 9) * f.colCurr 10) * (f.colCurr 11 * f.colCurr 29))) + (((f.colCurr 7 * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28))) * ((f.colCurr 23 - f.colNext 23) - 1))),
  -- Decoder.base[36]
  fun f => (f.is_transition * ((f.colCurr 23 - f.colNext 23) * ((((1 - f.colNext 9) * (1 - f.colNext 10)) * (f.colNext 11 * f.colNext 29)) + (((1 - f.colNext 9) * f.colNext 10) * (f.colNext 11 * f.colNext 29))))),
  -- Decoder.base[37]
  fun f => ((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) * f.colCurr 23),
  -- Decoder.base[38]
  fun f => (f.is_transition * ((((((((1 - f.colCurr 7) * f.colCurr 8) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28)) + (((1 - f.colCurr 9) * f.colCurr 10) * (f.colCurr 11 * f.colCurr 29))) + (((f.colCurr 7 * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28))) + ((f.colCurr 22 * f.colNext 22) * (1 - (f.colCurr 23 - f.colNext 23)))) * ((f.colCurr 14 - (f.colNext 14 * Felt.ofNat 128)) - ((((((f.colNext 7 + (f.colNext 8 * Felt.ofNat 2)) + (f.colNext 9 * Felt.ofNat 4)) + (f.colNext 10 * Felt.ofNat 8)) + (f.colNext 11 * Felt.ofNat 16)) + (f.colNext 12 * Felt.ofNat 32)) + (f.colNext 13 * Felt.ofNat 64))))),
  -- Decoder.base[39]
  fun f => (f.is_transition * ((f.colCurr 22 * ((((1 - f.colNext 9) * (1 - f.colNext 10)) * (f.colNext 11 * f.colNext 29)) + (((1 - f.colNext 9) * f.colNext 10) * (f.colNext 11 * f.colNext 29)))) * f.colCurr 14))
]

private def base_40_to_56 : List SymbolicConstraint := [
  -- Decoder.base[40]
  fun f => (f.is_transition * ((((((1 - f.colCurr 7) * f.colCurr 8) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28)) + (((1 - f.colCurr 9) * f.colCurr 10) * (f.colCurr 11 * f.colCurr 29))) * f.colNext 24)),
  -- Decoder.base[41]
  fun f => (f.is_transition * ((f.colCurr 22 * ((f.colCurr 23 - f.colNext 23) - (((f.colCurr 7 * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)))) * f.colNext 24)),
  -- Decoder.base[42]
  fun f => (f.is_transition * (((f.colCurr 22 * f.colNext 22) * (1 - ((f.colCurr 23 - f.colNext 23) - (((f.colCurr 7 * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28))))) * ((f.colNext 24 - f.colCurr 24) - 1))),
  -- Decoder.base[43]
  fun f => ((((((((f.colCurr 24 * (f.colCurr 24 - 1)) * (f.colCurr 24 - Felt.ofNat 2)) * (f.colCurr 24 - Felt.ofNat 3)) * (f.colCurr 24 - Felt.ofNat 4)) * (f.colCurr 24 - Felt.ofNat 5)) * (f.colCurr 24 - Felt.ofNat 6)) * (f.colCurr 24 - Felt.ofNat 7)) * (f.colCurr 24 - Felt.ofNat 8)),
  -- Decoder.base[44]
  fun f => ((((((1 - f.colCurr 7) * f.colCurr 8) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28)) + (((1 - f.colCurr 9) * f.colCurr 10) * (f.colCurr 11 * f.colCurr 29))) - ((((((1 - f.colCurr 25) * f.colCurr 26) * f.colCurr 27) + (((1 - f.colCurr 25) * (1 - f.colCurr 26)) * f.colCurr 27)) + (((1 - f.colCurr 25) * f.colCurr 26) * (1 - f.colCurr 27))) + f.colCurr 25)),
  -- Decoder.base[45]
  fun f => ((1 - (((((1 - f.colCurr 7) * f.colCurr 8) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28)) + (((1 - f.colCurr 9) * f.colCurr 10) * (f.colCurr 11 * f.colCurr 29)))) * ((f.colCurr 25 + f.colCurr 26) + f.colCurr 27)),
  -- Decoder.base[46]
  fun f => ((((((1 - f.colCurr 25) * f.colCurr 26) * f.colCurr 27) + (((1 - f.colCurr 25) * (1 - f.colCurr 26)) * f.colCurr 27)) + (((1 - f.colCurr 25) * f.colCurr 26) * (1 - f.colCurr 27))) * f.h 2),
  -- Decoder.base[47]
  fun f => ((((((1 - f.colCurr 25) * f.colCurr 26) * f.colCurr 27) + (((1 - f.colCurr 25) * (1 - f.colCurr 26)) * f.colCurr 27)) + (((1 - f.colCurr 25) * f.colCurr 26) * (1 - f.colCurr 27))) * f.h 3),
  -- Decoder.base[48]
  fun f => ((((((1 - f.colCurr 25) * f.colCurr 26) * f.colCurr 27) + (((1 - f.colCurr 25) * (1 - f.colCurr 26)) * f.colCurr 27)) + (((1 - f.colCurr 25) * f.colCurr 26) * (1 - f.colCurr 27))) * f.h 4),
  -- Decoder.base[49]
  fun f => ((((((1 - f.colCurr 25) * f.colCurr 26) * f.colCurr 27) + (((1 - f.colCurr 25) * (1 - f.colCurr 26)) * f.colCurr 27)) + (((1 - f.colCurr 25) * f.colCurr 26) * (1 - f.colCurr 27))) * f.h 5),
  -- Decoder.base[50]
  fun f => (((((1 - f.colCurr 25) * f.colCurr 26) * f.colCurr 27) + (((1 - f.colCurr 25) * (1 - f.colCurr 26)) * f.colCurr 27)) * f.h 0),
  -- Decoder.base[51]
  fun f => (((((1 - f.colCurr 25) * f.colCurr 26) * f.colCurr 27) + (((1 - f.colCurr 25) * (1 - f.colCurr 26)) * f.colCurr 27)) * f.h 1),
  -- Decoder.base[52]
  fun f => ((((1 - f.colCurr 25) * f.colCurr 26) * f.colCurr 27) * f.colCurr 15),
  -- Decoder.base[53]
  fun f => (f.is_transition * (f.colCurr 22 * (f.colNext 6 - f.colCurr 6))),
  -- Decoder.base[54]
  fun f => (f.is_transition * ((((1 - f.colCurr 9) * f.colCurr 10) * (f.colCurr 11 * f.colCurr 29)) * ((f.colNext 6 - f.colCurr 6) - Felt.ofNat 32))),
  -- Decoder.base[55]
  fun f => (((f.colCurr 9 * f.colCurr 10) * (f.colCurr 11 * f.colCurr 29)) * f.colCurr 6),
  -- Decoder.base[56]
  fun f => ((1 - f.colCurr 22) - (((((((f.colCurr 28 * (1 - f.colCurr 10)) * f.colCurr 9) + (f.colCurr 29 * f.colCurr 11)) + ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28))) + ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * (f.colCurr 10 * f.colCurr 28))) + (((1 - f.colCurr 9) * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29))) + ((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29))))
]

def base : List SymbolicConstraint :=
  base_0_to_19 ++ base_20_to_39 ++ base_40_to_56

end MidenLean.AIR.Constraints.Symbolic.Decoder
