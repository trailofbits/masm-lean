import MidenLean.AIR.SymbolicFrame
/-! ChipletMemory AIR constraints: 21 base + 0 ext. Auto-extracted. -/

namespace MidenLean.AIR.Constraints.Symbolic.ChipletMemory

open MidenLean MidenLean.AIR

private def base_0_to_19 : List SymbolicConstraint := [
  -- ChipletMemory.base[0]
  fun f => ((((f.colCurr 51 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54) * (f.colCurr 54 - 1)),
  -- ChipletMemory.base[1]
  fun f => ((((f.colCurr 51 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 55) * (f.colCurr 55 - 1)),
  -- ChipletMemory.base[2]
  fun f => ((((f.colCurr 51 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 58) * (f.colCurr 58 - 1)),
  -- ChipletMemory.base[3]
  fun f => ((((f.colCurr 51 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 59) * (f.colCurr 59 - 1)),
  -- ChipletMemory.base[4]
  fun f => ((((f.colCurr 51 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 55) * f.colCurr 58),
  -- ChipletMemory.base[5]
  fun f => ((((f.colCurr 51 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 55) * f.colCurr 59),
  -- ChipletMemory.base[6]
  fun f => (((f.is_transition * ((((1 - f.colCurr 52) * f.colCurr 51) * f.colNext 52) * (1 - f.colNext 53))) * (f.colNext 54 + (((1 - f.colNext 54) * (1 - f.colNext 55)) * (1 - ((1 - f.colNext 59) * (1 - f.colNext 58)))))) * f.colNext 61),
  -- ChipletMemory.base[7]
  fun f => (((f.is_transition * ((((1 - f.colCurr 52) * f.colCurr 51) * f.colNext 52) * (1 - f.colNext 53))) * (f.colNext 54 + (((1 - f.colNext 54) * (1 - f.colNext 55)) * (1 - ((1 - f.colNext 59) * f.colNext 58))))) * f.colNext 62),
  -- ChipletMemory.base[8]
  fun f => (((f.is_transition * ((((1 - f.colCurr 52) * f.colCurr 51) * f.colNext 52) * (1 - f.colNext 53))) * (f.colNext 54 + (((1 - f.colNext 54) * (1 - f.colNext 55)) * (1 - (f.colNext 59 * (1 - f.colNext 58)))))) * f.colNext 63),
  -- ChipletMemory.base[9]
  fun f => (((f.is_transition * ((((1 - f.colCurr 52) * f.colCurr 51) * f.colNext 52) * (1 - f.colNext 53))) * (f.colNext 54 + (((1 - f.colNext 54) * (1 - f.colNext 55)) * (1 - (f.colNext 59 * f.colNext 58))))) * f.colNext 64),
  -- ChipletMemory.base[10]
  fun f => (((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) * ((f.colNext 56 - f.colCurr 56) * f.colNext 67)) * (((f.colNext 56 - f.colCurr 56) * f.colNext 67) - 1)),
  -- ChipletMemory.base[11]
  fun f => (((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) * (1 - ((f.colNext 56 - f.colCurr 56) * f.colNext 67))) * (f.colNext 56 - f.colCurr 56)),
  -- ChipletMemory.base[12]
  fun f => ((((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) * (1 - ((f.colNext 56 - f.colCurr 56) * f.colNext 67))) * ((f.colNext 57 - f.colCurr 57) * f.colNext 67)) * (((f.colNext 57 - f.colCurr 57) * f.colNext 67) - 1)),
  -- ChipletMemory.base[13]
  fun f => ((((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) * (1 - ((f.colNext 56 - f.colCurr 56) * f.colNext 67))) * (1 - ((f.colNext 57 - f.colCurr 57) * f.colNext 67))) * (f.colNext 57 - f.colCurr 57)),
  -- ChipletMemory.base[14]
  fun f => ((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) * (((((f.colNext 56 - f.colCurr 56) * f.colNext 67) * (f.colNext 56 - f.colCurr 56)) + ((1 - ((f.colNext 56 - f.colCurr 56) * f.colNext 67)) * ((((f.colNext 57 - f.colCurr 57) * f.colNext 67) * (f.colNext 57 - f.colCurr 57)) + ((1 - ((f.colNext 57 - f.colCurr 57) * f.colNext 67)) * (f.colNext 60 - f.colCurr 60))))) - ((f.colNext 66 * Felt.ofNat 65536) + f.colNext 65))),
  -- ChipletMemory.base[15]
  fun f => ((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) * (f.colNext 68 - ((1 - ((f.colNext 56 - f.colCurr 56) * f.colNext 67)) * (1 - ((f.colNext 57 - f.colCurr 57) * f.colNext 67))))),
  -- ChipletMemory.base[16]
  fun f => ((((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) * f.colNext 68) * (1 - ((f.colNext 60 - f.colCurr 60) * f.colNext 67))) * ((1 - f.colCurr 54) + (1 - f.colNext 54))),
  -- ChipletMemory.base[17]
  fun f => (((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) * (f.colNext 54 + (((1 - f.colNext 54) * (1 - f.colNext 55)) * (1 - ((1 - f.colNext 59) * (1 - f.colNext 58)))))) * (f.colNext 61 - (f.colNext 68 * f.colCurr 61))),
  -- ChipletMemory.base[18]
  fun f => (((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) * (f.colNext 54 + (((1 - f.colNext 54) * (1 - f.colNext 55)) * (1 - ((1 - f.colNext 59) * f.colNext 58))))) * (f.colNext 62 - (f.colNext 68 * f.colCurr 62))),
  -- ChipletMemory.base[19]
  fun f => (((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) * (f.colNext 54 + (((1 - f.colNext 54) * (1 - f.colNext 55)) * (1 - (f.colNext 59 * (1 - f.colNext 58)))))) * (f.colNext 63 - (f.colNext 68 * f.colCurr 63)))
]

private def base_20_to_20 : List SymbolicConstraint := [
  -- ChipletMemory.base[20]
  fun f => (((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) * (f.colNext 54 + (((1 - f.colNext 54) * (1 - f.colNext 55)) * (1 - (f.colNext 59 * f.colNext 58))))) * (f.colNext 64 - (f.colNext 68 * f.colCurr 64)))
]

def base : List SymbolicConstraint :=
  base_0_to_19 ++ base_20_to_20

end MidenLean.AIR.Constraints.Symbolic.ChipletMemory
