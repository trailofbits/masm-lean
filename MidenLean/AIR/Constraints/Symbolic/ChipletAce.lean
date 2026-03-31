import MidenLean.AIR.SymbolicFrame
set_option maxHeartbeats 8000000
/-! ChipletAce AIR constraints: 20 base + 0 ext. Auto-extracted. -/

namespace MidenLean.AIR.Constraints.Symbolic.ChipletAce

open MidenLean MidenLean.AIR

def base : List SymbolicConstraint := [
  -- ChipletAce.base[0]
  fun f => (((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * f.colCurr 55) * (f.colCurr 55 - 1)),
  -- ChipletAce.base[1]
  fun f => (((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * f.colCurr 56) * (f.colCurr 56 - 1)),
  -- ChipletAce.base[2]
  fun f => (((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * (f.is_transition * f.colNext 54)) * f.colCurr 55),
  -- ChipletAce.base[3]
  fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * (f.is_transition * (1 - f.colNext 54))) * f.colCurr 55) * f.colNext 55),
  -- ChipletAce.base[4]
  fun f => (((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * f.colCurr 55) * f.colCurr 56),
  -- ChipletAce.base[5]
  fun f => (((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * (f.is_transition * (1 - f.colNext 54))) * (1 - f.colNext 55)) * f.colCurr 56) * (1 - f.colNext 56)),
  -- ChipletAce.base[6]
  fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * f.is_transition) * ((((1 - f.colNext 54) * f.colNext 55) + f.colNext 54) - (((1 - f.colNext 54) * f.colNext 55) * f.colNext 54))) * (1 - f.colCurr 56)),
  -- ChipletAce.base[7]
  fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * (f.is_transition * (1 - f.colNext 54))) * (1 - f.colNext 55)) * (f.colNext 57 - f.colCurr 57)),
  -- ChipletAce.base[8]
  fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * (f.is_transition * (1 - f.colNext 54))) * (1 - f.colNext 55)) * (f.colNext 59 - f.colCurr 59)),
  -- ChipletAce.base[9]
  fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * (f.is_transition * (1 - f.colNext 54))) * (1 - f.colNext 55)) * (f.colNext 58 - ((f.colCurr 58 + (Felt.ofNat 4 * (1 - f.colCurr 56))) + f.colCurr 56))),
  -- ChipletAce.base[10]
  fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * (f.is_transition * (1 - f.colNext 54))) * (1 - f.colNext 55)) * (f.colCurr 61 - ((f.colNext 61 + ((1 - f.colCurr 56) + (1 - f.colCurr 56))) + f.colCurr 56))),
  -- ChipletAce.base[11]
  fun f => (((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * (1 - f.colCurr 56)) * ((f.colCurr 64 - f.colCurr 61) + 1)),
  -- ChipletAce.base[12]
  fun f => (((f.is_transition * (((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) * (1 - f.colCurr 56)) * ((((1 - f.colNext 56) * f.colNext 67) + (f.colNext 56 * f.colNext 61)) - f.colCurr 67)),
  -- ChipletAce.base[13]
  fun f => (((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * f.colCurr 56) * f.colCurr 60) * (f.colCurr 60 - 1)) * (f.colCurr 60 + 1)),
  -- ChipletAce.base[14]
  fun f => (((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * f.colCurr 56) * ((((f.colCurr 60 * f.colCurr 60) * ((f.colCurr 65 + (f.colCurr 68 * f.colCurr 60)) - ((f.colCurr 65 * f.colCurr 68) + (Felt.ofNat 7 * (f.colCurr 66 * f.colCurr 69))))) + ((f.colCurr 65 * f.colCurr 68) + (Felt.ofNat 7 * (f.colCurr 66 * f.colCurr 69)))) - f.colCurr 62)),
  -- ChipletAce.base[15]
  fun f => (((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * f.colCurr 56) * ((((f.colCurr 60 * f.colCurr 60) * ((f.colCurr 66 + (f.colCurr 69 * f.colCurr 60)) - ((f.colCurr 65 * f.colCurr 69) + (f.colCurr 66 * f.colCurr 68)))) + ((f.colCurr 65 * f.colCurr 69) + (f.colCurr 66 * f.colCurr 68))) - f.colCurr 63)),
  -- ChipletAce.base[16]
  fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * f.is_transition) * ((((1 - f.colNext 54) * f.colNext 55) + f.colNext 54) - (((1 - f.colNext 54) * f.colNext 55) * f.colNext 54))) * f.colCurr 62),
  -- ChipletAce.base[17]
  fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * f.is_transition) * ((((1 - f.colNext 54) * f.colNext 55) + f.colNext 54) - (((1 - f.colNext 54) * f.colNext 55) * f.colNext 54))) * f.colCurr 63),
  -- ChipletAce.base[18]
  fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * f.is_transition) * ((((1 - f.colNext 54) * f.colNext 55) + f.colNext 54) - (((1 - f.colNext 54) * f.colNext 55) * f.colNext 54))) * f.colCurr 61),
  -- ChipletAce.base[19]
  fun f => (((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colCurr 53))) * (f.colNext 53 * (1 - f.colNext 54))) * (f.colNext 55 - 1))
]

end MidenLean.AIR.Constraints.Symbolic.ChipletAce
