import MidenLean.AIR.SymbolicFrame
/-! StackArith AIR constraints: 42 base + 0 ext. Auto-extracted. -/

namespace MidenLean.AIR.Constraints.Symbolic.StackArith

open MidenLean MidenLean.AIR

private def base_0_to_19 : List SymbolicConstraint := [
  -- StackArith.base[0]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 - (f.s 0 + f.s 1)))),
  -- StackArith.base[1]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 + f.s 0))),
  -- StackArith.base[2]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * (f.s' 0 - (f.s 0 * f.s 1)))),
  -- StackArith.base[3]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * ((f.s' 0 * f.s 0) - 1))),
  -- StackArith.base[4]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * ((f.s' 0 - f.s 0) - 1))),
  -- StackArith.base[5]
  fun f => (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s 0 * (f.s 0 - 1))),
  -- StackArith.base[6]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * ((f.s 0 + f.s' 0) - 1))),
  -- StackArith.base[7]
  fun f => ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s 0 * (f.s 0 - 1))),
  -- StackArith.base[8]
  fun f => ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s 1 * (f.s 1 - 1))),
  -- StackArith.base[9]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 0 - (f.s 0 * f.s 1)))),
  -- StackArith.base[10]
  fun f => ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s 0 * (f.s 0 - 1))),
  -- StackArith.base[11]
  fun f => ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s 1 * (f.s 1 - 1))),
  -- StackArith.base[12]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 0 - ((f.s 0 + f.s 1) - (f.s 0 * f.s 1))))),
  -- StackArith.base[13]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * ((f.s 0 - f.s 1) * f.s' 0))),
  -- StackArith.base[14]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 0 - (1 - ((f.s 0 - f.s 1) * f.h 0))))),
  -- StackArith.base[15]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s 0 * f.s' 0))),
  -- StackArith.base[16]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 0 - (1 - (f.s 0 * f.h 0))))),
  -- StackArith.base[17]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * f.colCurr 7) * (f.s' 1 - (f.s 1 * f.s 1)))),
  -- StackArith.base[18]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * f.colCurr 7) * ((f.h 0 - 1) - ((f.s 1 - 1) * f.s' 0)))),
  -- StackArith.base[19]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * f.colCurr 7) * (f.s' 2 - (f.s 2 * f.h 0))))
]

private def base_20_to_39 : List SymbolicConstraint := [
  -- StackArith.base[20]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * f.colCurr 7) * ((f.s 3 - (f.s' 3 * Felt.ofNat 2)) - f.s' 0))),
  -- StackArith.base[21]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * f.colCurr 7) * (f.s' 0 * (f.s' 0 - 1)))),
  -- StackArith.base[22]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 0 - f.s 0))),
  -- StackArith.base[23]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 1 - f.s 1))),
  -- StackArith.base[24]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 2 - ((f.s 2 * f.s 0) + (Felt.ofNat 7 * (f.s 3 * f.s 1)))))),
  -- StackArith.base[25]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 3 - ((((f.s 2 + f.s 3) * (f.s 0 + f.s 1)) - (f.s 2 * f.s 0)) - (f.s 3 * f.s 1))))),
  -- StackArith.base[26]
  fun f => ((((((1 - f.colCurr 8) * ((1 - f.colCurr 9) * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) + (((1 - f.colCurr 8) * (f.colCurr 9 * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) + ((f.colCurr 8 * (f.colCurr 9 * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) * ((1 - (f.h 4 * (Felt.ofNat 4294967295 - ((f.h 3 * Felt.ofNat 65536) + f.h 2)))) * ((f.h 1 * Felt.ofNat 65536) + f.h 0))),
  -- StackArith.base[27]
  fun f => (f.is_transition * ((((((((1 - f.colCurr 8) * ((1 - f.colCurr 9) * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) + (((1 - f.colCurr 8) * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) + (((1 - f.colCurr 8) * (f.colCurr 9 * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) + (((1 - f.colCurr 8) * (f.colCurr 9 * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) + ((f.colCurr 8 * (f.colCurr 9 * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) * (f.s' 0 - ((f.h 1 * Felt.ofNat 65536) + f.h 0)))),
  -- StackArith.base[28]
  fun f => (f.is_transition * ((((((((1 - f.colCurr 8) * ((1 - f.colCurr 9) * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) + (((1 - f.colCurr 8) * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) + (((1 - f.colCurr 8) * (f.colCurr 9 * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) + (((1 - f.colCurr 8) * (f.colCurr 9 * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) + ((f.colCurr 8 * (f.colCurr 9 * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) * (f.s' 1 - ((f.h 3 * Felt.ofNat 65536) + f.h 2)))),
  -- StackArith.base[29]
  fun f => ((((1 - f.colCurr 8) * ((1 - f.colCurr 9) * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (f.s 0 - ((f.h 3 * Felt.ofNat 281474976710656) + ((f.h 2 * Felt.ofNat 4294967296) + ((f.h 1 * Felt.ofNat 65536) + f.h 0))))),
  -- StackArith.base[30]
  fun f => ((((1 - f.colCurr 8) * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * ((f.s 0 + f.s 1) - ((f.h 2 * Felt.ofNat 4294967296) + ((f.h 1 * Felt.ofNat 65536) + f.h 0)))),
  -- StackArith.base[31]
  fun f => ((((1 - f.colCurr 8) * (f.colCurr 9 * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (((f.s 0 + f.s 1) + f.s 2) - ((f.h 2 * Felt.ofNat 4294967296) + ((f.h 1 * Felt.ofNat 65536) + f.h 0)))),
  -- StackArith.base[32]
  fun f => (f.is_transition * (((f.colCurr 8 * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (f.s 1 - ((f.s 0 + f.s' 1) - (f.s' 0 * Felt.ofNat 4294967296))))),
  -- StackArith.base[33]
  fun f => (f.is_transition * (((f.colCurr 8 * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (f.s' 0 * (f.s' 0 - 1)))),
  -- StackArith.base[34]
  fun f => (f.is_transition * (((f.colCurr 8 * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (f.s' 1 - ((f.h 1 * Felt.ofNat 65536) + f.h 0)))),
  -- StackArith.base[35]
  fun f => ((((1 - f.colCurr 8) * (f.colCurr 9 * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * ((f.s 0 * f.s 1) - ((f.h 3 * Felt.ofNat 281474976710656) + ((f.h 2 * Felt.ofNat 4294967296) + ((f.h 1 * Felt.ofNat 65536) + f.h 0))))),
  -- StackArith.base[36]
  fun f => (((f.colCurr 8 * (f.colCurr 9 * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (((f.s 0 * f.s 1) + f.s 2) - ((f.h 3 * Felt.ofNat 281474976710656) + ((f.h 2 * Felt.ofNat 4294967296) + ((f.h 1 * Felt.ofNat 65536) + f.h 0))))),
  -- StackArith.base[37]
  fun f => (f.is_transition * (((f.colCurr 8 * (f.colCurr 9 * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (f.s 1 - ((f.s 0 * f.s' 1) + f.s' 0)))),
  -- StackArith.base[38]
  fun f => (f.is_transition * (((f.colCurr 8 * (f.colCurr 9 * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * ((f.s 1 - f.s' 1) - ((f.h 1 * Felt.ofNat 65536) + f.h 0)))),
  -- StackArith.base[39]
  fun f => (f.is_transition * (((f.colCurr 8 * (f.colCurr 9 * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * ((f.s 0 - f.s' 0) - (((f.h 3 * Felt.ofNat 65536) + f.h 2) + 1))))
]

private def base_40_to_41 : List SymbolicConstraint := [
  -- StackArith.base[40]
  fun f => (f.is_transition * (((f.colCurr 8 * ((1 - f.colCurr 9) * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (f.s' 0 - ((f.h 3 * Felt.ofNat 65536) + f.h 2)))),
  -- StackArith.base[41]
  fun f => (f.is_transition * (((f.colCurr 8 * ((1 - f.colCurr 9) * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (f.s' 1 - ((f.h 1 * Felt.ofNat 65536) + f.h 0))))
]

def base : List SymbolicConstraint :=
  base_0_to_19 ++ base_20_to_39 ++ base_40_to_41

end MidenLean.AIR.Constraints.Symbolic.StackArith
