import MidenLean.AIR.SymbolicFrame
set_option maxHeartbeats 8000000
/-! StackCrypto AIR constraints: 46 base + 0 ext. Auto-extracted. -/

namespace MidenLean.AIR.Constraints.Symbolic.StackCrypto

open MidenLean MidenLean.AIR

private def base_0_to_19 : List SymbolicConstraint := [
  -- StackCrypto.base[0]
  fun f => (f.is_transition * (((f.colCurr 9 * (1 - f.colCurr 10)) * ((1 - f.colCurr 11) * f.colCurr 29)) * (f.s' 8 - f.s 8))),
  -- StackCrypto.base[1]
  fun f => (f.is_transition * (((f.colCurr 9 * (1 - f.colCurr 10)) * ((1 - f.colCurr 11) * f.colCurr 29)) * (f.s' 9 - f.s 9))),
  -- StackCrypto.base[2]
  fun f => (f.is_transition * (((f.colCurr 9 * (1 - f.colCurr 10)) * ((1 - f.colCurr 11) * f.colCurr 29)) * (f.s' 10 - f.s 10))),
  -- StackCrypto.base[3]
  fun f => (f.is_transition * (((f.colCurr 9 * (1 - f.colCurr 10)) * ((1 - f.colCurr 11) * f.colCurr 29)) * (f.s' 11 - f.s 11))),
  -- StackCrypto.base[4]
  fun f => (f.is_transition * (((f.colCurr 9 * (1 - f.colCurr 10)) * ((1 - f.colCurr 11) * f.colCurr 29)) * (f.s' 12 - (f.s 12 + Felt.ofNat 8)))),
  -- StackCrypto.base[5]
  fun f => (f.is_transition * (((f.colCurr 9 * (1 - f.colCurr 10)) * ((1 - f.colCurr 11) * f.colCurr 29)) * (f.s' 13 - (f.s 13 + Felt.ofNat 8)))),
  -- StackCrypto.base[6]
  fun f => (f.is_transition * (((f.colCurr 9 * (1 - f.colCurr 10)) * ((1 - f.colCurr 11) * f.colCurr 29)) * (f.s' 14 - f.s 14))),
  -- StackCrypto.base[7]
  fun f => (f.is_transition * (((f.colCurr 9 * (1 - f.colCurr 10)) * ((1 - f.colCurr 11) * f.colCurr 29)) * (f.s' 15 - f.s 15))),
  -- StackCrypto.base[8]
  fun f => (f.is_transition * ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 0 - f.s 0))),
  -- StackCrypto.base[9]
  fun f => (f.is_transition * ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 1 - f.s 1))),
  -- StackCrypto.base[10]
  fun f => (f.is_transition * ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 2 - f.s 2))),
  -- StackCrypto.base[11]
  fun f => (f.is_transition * ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 3 - f.s 3))),
  -- StackCrypto.base[12]
  fun f => (f.is_transition * ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 4 - f.s 4))),
  -- StackCrypto.base[13]
  fun f => (f.is_transition * ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 5 - f.s 5))),
  -- StackCrypto.base[14]
  fun f => (f.is_transition * ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 6 - f.s 6))),
  -- StackCrypto.base[15]
  fun f => (f.is_transition * ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 7 - f.s 7))),
  -- StackCrypto.base[16]
  fun f => (f.is_transition * ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 8 - f.s 8))),
  -- StackCrypto.base[17]
  fun f => (f.is_transition * ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 9 - f.s 9))),
  -- StackCrypto.base[18]
  fun f => (f.is_transition * ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 10 - f.s 10))),
  -- StackCrypto.base[19]
  fun f => (f.is_transition * ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 11 - f.s 11)))
]

private def base_20_to_39 : List SymbolicConstraint := [
  -- StackCrypto.base[20]
  fun f => (f.is_transition * ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 12 - f.s 12))),
  -- StackCrypto.base[21]
  fun f => (f.is_transition * ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 13 - f.s 13))),
  -- StackCrypto.base[22]
  fun f => ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.h 4 - ((((f.s 14 * ((f.h 0 * f.h 0) + (Felt.ofNat 7 * (f.h 1 * f.h 1)))) + (Felt.ofNat 7 * (f.s 15 * ((f.h 0 * f.h 1) + (f.h 0 * f.h 1))))) + (f.h 0 * f.s 0)) + f.s 1))),
  -- StackCrypto.base[23]
  fun f => ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.h 5 - (((f.s 14 * ((f.h 0 * f.h 1) + (f.h 0 * f.h 1))) + (f.s 15 * ((f.h 0 * f.h 0) + (Felt.ofNat 7 * (f.h 1 * f.h 1))))) + (f.h 1 * f.s 0)))),
  -- StackCrypto.base[24]
  fun f => ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.h 2 - (((((f.h 4 * ((((f.h 0 * f.h 0) + (Felt.ofNat 7 * (f.h 1 * f.h 1))) * f.h 0) + (Felt.ofNat 7 * (((f.h 0 * f.h 1) + (f.h 0 * f.h 1)) * f.h 1)))) + (Felt.ofNat 7 * (f.h 5 * ((((f.h 0 * f.h 0) + (Felt.ofNat 7 * (f.h 1 * f.h 1))) * f.h 1) + (((f.h 0 * f.h 1) + (f.h 0 * f.h 1)) * f.h 0))))) + (((f.h 0 * f.h 0) + (Felt.ofNat 7 * (f.h 1 * f.h 1))) * f.s 2)) + (f.h 0 * f.s 3)) + f.s 4))),
  -- StackCrypto.base[25]
  fun f => ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.h 3 - ((((f.h 4 * ((((f.h 0 * f.h 0) + (Felt.ofNat 7 * (f.h 1 * f.h 1))) * f.h 1) + (((f.h 0 * f.h 1) + (f.h 0 * f.h 1)) * f.h 0))) + (f.h 5 * ((((f.h 0 * f.h 0) + (Felt.ofNat 7 * (f.h 1 * f.h 1))) * f.h 0) + (Felt.ofNat 7 * (((f.h 0 * f.h 1) + (f.h 0 * f.h 1)) * f.h 1))))) + (((f.h 0 * f.h 1) + (f.h 0 * f.h 1)) * f.s 2)) + (f.h 1 * f.s 3)))),
  -- StackCrypto.base[26]
  fun f => (f.is_transition * ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 14 - (((((f.h 2 * ((((f.h 0 * f.h 0) + (Felt.ofNat 7 * (f.h 1 * f.h 1))) * f.h 0) + (Felt.ofNat 7 * (((f.h 0 * f.h 1) + (f.h 0 * f.h 1)) * f.h 1)))) + (Felt.ofNat 7 * (f.h 3 * ((((f.h 0 * f.h 0) + (Felt.ofNat 7 * (f.h 1 * f.h 1))) * f.h 1) + (((f.h 0 * f.h 1) + (f.h 0 * f.h 1)) * f.h 0))))) + (((f.h 0 * f.h 0) + (Felt.ofNat 7 * (f.h 1 * f.h 1))) * f.s 5)) + (f.h 0 * f.s 6)) + f.s 7)))),
  -- StackCrypto.base[27]
  fun f => (f.is_transition * ((((f.colCurr 7 * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 15 - ((((f.h 2 * ((((f.h 0 * f.h 0) + (Felt.ofNat 7 * (f.h 1 * f.h 1))) * f.h 1) + (((f.h 0 * f.h 1) + (f.h 0 * f.h 1)) * f.h 0))) + (f.h 3 * ((((f.h 0 * f.h 0) + (Felt.ofNat 7 * (f.h 1 * f.h 1))) * f.h 0) + (Felt.ofNat 7 * (((f.h 0 * f.h 1) + (f.h 0 * f.h 1)) * f.h 1))))) + (((f.h 0 * f.h 1) + (f.h 0 * f.h 1)) * f.s 5)) + (f.h 1 * f.s 6))))),
  -- StackCrypto.base[28]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 0 - f.s 0))),
  -- StackCrypto.base[29]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 1 - f.s 1))),
  -- StackCrypto.base[30]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 2 - f.s 2))),
  -- StackCrypto.base[31]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 3 - f.s 3))),
  -- StackCrypto.base[32]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 4 - f.s 4))),
  -- StackCrypto.base[33]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 5 - f.s 5))),
  -- StackCrypto.base[34]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 6 - f.s 6))),
  -- StackCrypto.base[35]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 7 - f.s 7))),
  -- StackCrypto.base[36]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 8 - f.s 8))),
  -- StackCrypto.base[37]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 9 - f.s 9))),
  -- StackCrypto.base[38]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 10 - f.s 10))),
  -- StackCrypto.base[39]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 11 - f.s 11)))
]

private def base_40_to_45 : List SymbolicConstraint := [
  -- StackCrypto.base[40]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 12 - f.s 12))),
  -- StackCrypto.base[41]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 13 - f.s 13))),
  -- StackCrypto.base[42]
  fun f => (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.h 4 - ((((f.s 14 * ((f.h 0 * f.h 0) + (Felt.ofNat 7 * (f.h 1 * f.h 1)))) + (Felt.ofNat 7 * (f.s 15 * ((f.h 0 * f.h 1) + (f.h 0 * f.h 1))))) + ((f.h 0 * f.s 0) + (Felt.ofNat 7 * (f.h 1 * f.s 1)))) + f.s 2))),
  -- StackCrypto.base[43]
  fun f => (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.h 5 - ((((f.s 14 * ((f.h 0 * f.h 1) + (f.h 0 * f.h 1))) + (f.s 15 * ((f.h 0 * f.h 0) + (Felt.ofNat 7 * (f.h 1 * f.h 1))))) + ((f.h 0 * f.s 1) + (f.h 1 * f.s 0))) + f.s 3))),
  -- StackCrypto.base[44]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 14 - ((((f.h 4 * ((f.h 0 * f.h 0) + (Felt.ofNat 7 * (f.h 1 * f.h 1)))) + (Felt.ofNat 7 * (f.h 5 * ((f.h 0 * f.h 1) + (f.h 0 * f.h 1))))) + ((f.h 0 * f.s 4) + (Felt.ofNat 7 * (f.h 1 * f.s 5)))) + f.s 6)))),
  -- StackCrypto.base[45]
  fun f => (f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) * (f.s' 15 - ((((f.h 4 * ((f.h 0 * f.h 1) + (f.h 0 * f.h 1))) + (f.h 5 * ((f.h 0 * f.h 0) + (Felt.ofNat 7 * (f.h 1 * f.h 1))))) + ((f.h 0 * f.s 5) + (f.h 1 * f.s 4))) + f.s 7))))
]

def base : List SymbolicConstraint :=
  base_0_to_19 ++ base_20_to_39 ++ base_40_to_45

end MidenLean.AIR.Constraints.Symbolic.StackCrypto
