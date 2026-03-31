import MidenLean.AIR.SymbolicFrame
set_option maxHeartbeats 8000000
/-! ChipletBitwise AIR constraints: 17 base + 0 ext. Auto-extracted. -/

namespace MidenLean.AIR.Constraints.Symbolic.ChipletBitwise

open MidenLean MidenLean.AIR

def base : List SymbolicConstraint := [
  -- ChipletBitwise.base[0]
  fun f => (((f.colCurr 51 * (1 - f.colCurr 52)) * f.colCurr 53) * (f.colCurr 53 - 1)),
  -- ChipletBitwise.base[1]
  fun f => ((f.periodic 19 * (f.colCurr 51 * (1 - f.colCurr 52))) * (f.colCurr 53 - f.colNext 53)),
  -- ChipletBitwise.base[2]
  fun f => (((f.colCurr 51 * (1 - f.colCurr 52)) * f.colCurr 56) * (f.colCurr 56 - 1)),
  -- ChipletBitwise.base[3]
  fun f => (((f.colCurr 51 * (1 - f.colCurr 52)) * f.colCurr 57) * (f.colCurr 57 - 1)),
  -- ChipletBitwise.base[4]
  fun f => (((f.colCurr 51 * (1 - f.colCurr 52)) * f.colCurr 58) * (f.colCurr 58 - 1)),
  -- ChipletBitwise.base[5]
  fun f => (((f.colCurr 51 * (1 - f.colCurr 52)) * f.colCurr 59) * (f.colCurr 59 - 1)),
  -- ChipletBitwise.base[6]
  fun f => (((f.colCurr 51 * (1 - f.colCurr 52)) * f.colCurr 60) * (f.colCurr 60 - 1)),
  -- ChipletBitwise.base[7]
  fun f => (((f.colCurr 51 * (1 - f.colCurr 52)) * f.colCurr 61) * (f.colCurr 61 - 1)),
  -- ChipletBitwise.base[8]
  fun f => (((f.colCurr 51 * (1 - f.colCurr 52)) * f.colCurr 62) * (f.colCurr 62 - 1)),
  -- ChipletBitwise.base[9]
  fun f => (((f.colCurr 51 * (1 - f.colCurr 52)) * f.colCurr 63) * (f.colCurr 63 - 1)),
  -- ChipletBitwise.base[10]
  fun f => ((f.periodic 18 * (f.colCurr 51 * (1 - f.colCurr 52))) * (f.colCurr 54 - ((((((f.colCurr 59 + f.colCurr 59) + f.colCurr 58) + ((f.colCurr 59 + f.colCurr 59) + f.colCurr 58)) + f.colCurr 57) + ((((f.colCurr 59 + f.colCurr 59) + f.colCurr 58) + ((f.colCurr 59 + f.colCurr 59) + f.colCurr 58)) + f.colCurr 57)) + f.colCurr 56))),
  -- ChipletBitwise.base[11]
  fun f => ((f.periodic 18 * (f.colCurr 51 * (1 - f.colCurr 52))) * (f.colCurr 55 - ((((((f.colCurr 63 + f.colCurr 63) + f.colCurr 62) + ((f.colCurr 63 + f.colCurr 63) + f.colCurr 62)) + f.colCurr 61) + ((((f.colCurr 63 + f.colCurr 63) + f.colCurr 62) + ((f.colCurr 63 + f.colCurr 63) + f.colCurr 62)) + f.colCurr 61)) + f.colCurr 60))),
  -- ChipletBitwise.base[12]
  fun f => ((f.periodic 18 * (f.colCurr 51 * (1 - f.colCurr 52))) * f.colCurr 64),
  -- ChipletBitwise.base[13]
  fun f => ((f.periodic 19 * (f.colCurr 51 * (1 - f.colCurr 52))) * (f.colNext 54 - ((f.colCurr 54 * Felt.ofNat 16) + ((((((f.colNext 59 + f.colNext 59) + f.colNext 58) + ((f.colNext 59 + f.colNext 59) + f.colNext 58)) + f.colNext 57) + ((((f.colNext 59 + f.colNext 59) + f.colNext 58) + ((f.colNext 59 + f.colNext 59) + f.colNext 58)) + f.colNext 57)) + f.colNext 56)))),
  -- ChipletBitwise.base[14]
  fun f => ((f.periodic 19 * (f.colCurr 51 * (1 - f.colCurr 52))) * (f.colNext 55 - ((f.colCurr 55 * Felt.ofNat 16) + ((((((f.colNext 63 + f.colNext 63) + f.colNext 62) + ((f.colNext 63 + f.colNext 63) + f.colNext 62)) + f.colNext 61) + ((((f.colNext 63 + f.colNext 63) + f.colNext 62) + ((f.colNext 63 + f.colNext 63) + f.colNext 62)) + f.colNext 61)) + f.colNext 60)))),
  -- ChipletBitwise.base[15]
  fun f => ((f.periodic 19 * (f.colCurr 51 * (1 - f.colCurr 52))) * (f.colNext 64 - f.colCurr 65)),
  -- ChipletBitwise.base[16]
  fun f => ((f.colCurr 51 * (1 - f.colCurr 52)) * (f.colCurr 65 - (((f.colCurr 64 * Felt.ofNat 16) + (((((((f.colCurr 59 * f.colCurr 63) + (f.colCurr 59 * f.colCurr 63)) + (f.colCurr 58 * f.colCurr 62)) + (((f.colCurr 59 * f.colCurr 63) + (f.colCurr 59 * f.colCurr 63)) + (f.colCurr 58 * f.colCurr 62))) + (f.colCurr 57 * f.colCurr 61)) + (((((f.colCurr 59 * f.colCurr 63) + (f.colCurr 59 * f.colCurr 63)) + (f.colCurr 58 * f.colCurr 62)) + (((f.colCurr 59 * f.colCurr 63) + (f.colCurr 59 * f.colCurr 63)) + (f.colCurr 58 * f.colCurr 62))) + (f.colCurr 57 * f.colCurr 61))) + (f.colCurr 56 * f.colCurr 60))) + (f.colCurr 53 * (((((((((f.colCurr 59 + f.colCurr 63) - ((f.colCurr 59 * f.colCurr 63) + (f.colCurr 59 * f.colCurr 63))) + ((f.colCurr 59 + f.colCurr 63) - ((f.colCurr 59 * f.colCurr 63) + (f.colCurr 59 * f.colCurr 63)))) + ((f.colCurr 58 + f.colCurr 62) - ((f.colCurr 58 * f.colCurr 62) + (f.colCurr 58 * f.colCurr 62)))) + ((((f.colCurr 59 + f.colCurr 63) - ((f.colCurr 59 * f.colCurr 63) + (f.colCurr 59 * f.colCurr 63))) + ((f.colCurr 59 + f.colCurr 63) - ((f.colCurr 59 * f.colCurr 63) + (f.colCurr 59 * f.colCurr 63)))) + ((f.colCurr 58 + f.colCurr 62) - ((f.colCurr 58 * f.colCurr 62) + (f.colCurr 58 * f.colCurr 62))))) + ((f.colCurr 57 + f.colCurr 61) - ((f.colCurr 57 * f.colCurr 61) + (f.colCurr 57 * f.colCurr 61)))) + ((((((f.colCurr 59 + f.colCurr 63) - ((f.colCurr 59 * f.colCurr 63) + (f.colCurr 59 * f.colCurr 63))) + ((f.colCurr 59 + f.colCurr 63) - ((f.colCurr 59 * f.colCurr 63) + (f.colCurr 59 * f.colCurr 63)))) + ((f.colCurr 58 + f.colCurr 62) - ((f.colCurr 58 * f.colCurr 62) + (f.colCurr 58 * f.colCurr 62)))) + ((((f.colCurr 59 + f.colCurr 63) - ((f.colCurr 59 * f.colCurr 63) + (f.colCurr 59 * f.colCurr 63))) + ((f.colCurr 59 + f.colCurr 63) - ((f.colCurr 59 * f.colCurr 63) + (f.colCurr 59 * f.colCurr 63)))) + ((f.colCurr 58 + f.colCurr 62) - ((f.colCurr 58 * f.colCurr 62) + (f.colCurr 58 * f.colCurr 62))))) + ((f.colCurr 57 + f.colCurr 61) - ((f.colCurr 57 * f.colCurr 61) + (f.colCurr 57 * f.colCurr 61))))) + ((f.colCurr 56 + f.colCurr 60) - ((f.colCurr 56 * f.colCurr 60) + (f.colCurr 56 * f.colCurr 60)))) - (((((((f.colCurr 59 * f.colCurr 63) + (f.colCurr 59 * f.colCurr 63)) + (f.colCurr 58 * f.colCurr 62)) + (((f.colCurr 59 * f.colCurr 63) + (f.colCurr 59 * f.colCurr 63)) + (f.colCurr 58 * f.colCurr 62))) + (f.colCurr 57 * f.colCurr 61)) + (((((f.colCurr 59 * f.colCurr 63) + (f.colCurr 59 * f.colCurr 63)) + (f.colCurr 58 * f.colCurr 62)) + (((f.colCurr 59 * f.colCurr 63) + (f.colCurr 59 * f.colCurr 63)) + (f.colCurr 58 * f.colCurr 62))) + (f.colCurr 57 * f.colCurr 61))) + (f.colCurr 56 * f.colCurr 60)))))))
]

end MidenLean.AIR.Constraints.Symbolic.ChipletBitwise
