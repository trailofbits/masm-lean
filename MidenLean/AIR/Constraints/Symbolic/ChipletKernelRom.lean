import MidenLean.AIR.SymbolicFrame
/-! ChipletKernelRom AIR constraints: 6 base + 0 ext. Auto-extracted. -/

namespace MidenLean.AIR.Constraints.Symbolic.ChipletKernelRom

open MidenLean MidenLean.AIR

def base : List SymbolicConstraint := [
  -- ChipletKernelRom.base[0]
  fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54) * (1 - f.colCurr 55)) * f.colCurr 56) * (f.colCurr 56 - 1)),
  -- ChipletKernelRom.base[1]
  fun f => (f.is_transition * ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54) * (1 - f.colCurr 55)) * ((1 - f.colNext 55) * (1 - f.colNext 56))) * (f.colNext 57 - f.colCurr 57))),
  -- ChipletKernelRom.base[2]
  fun f => (f.is_transition * ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54) * (1 - f.colCurr 55)) * ((1 - f.colNext 55) * (1 - f.colNext 56))) * (f.colNext 58 - f.colCurr 58))),
  -- ChipletKernelRom.base[3]
  fun f => (f.is_transition * ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54) * (1 - f.colCurr 55)) * ((1 - f.colNext 55) * (1 - f.colNext 56))) * (f.colNext 59 - f.colCurr 59))),
  -- ChipletKernelRom.base[4]
  fun f => (f.is_transition * ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54) * (1 - f.colCurr 55)) * ((1 - f.colNext 55) * (1 - f.colNext 56))) * (f.colNext 60 - f.colCurr 60))),
  -- ChipletKernelRom.base[5]
  fun f => (f.is_transition * (((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54)) * (f.colNext 54 * (1 - f.colNext 55))) * (f.colNext 56 - 1)))
]

end MidenLean.AIR.Constraints.Symbolic.ChipletKernelRom
