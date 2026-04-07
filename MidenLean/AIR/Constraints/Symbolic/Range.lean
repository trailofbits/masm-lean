import MidenLean.AIR.SymbolicFrame
/-! Range AIR constraints: 3 base + 0 ext. Auto-extracted. -/

namespace MidenLean.AIR.Constraints.Symbolic.Range

open MidenLean MidenLean.AIR

def base : List SymbolicConstraint := [
  -- Range.base[0]
  fun f => (f.is_first_row * f.colCurr 50),
  -- Range.base[1]
  fun f => (f.is_last_row * (f.colCurr 50 - Felt.ofNat 65535)),
  -- Range.base[2]
  fun f => (f.is_transition * (((((((((f.colNext 50 - f.colCurr 50) * ((f.colNext 50 - f.colCurr 50) - 1)) * ((f.colNext 50 - f.colCurr 50) - Felt.ofNat 3)) * ((f.colNext 50 - f.colCurr 50) - Felt.ofNat 9)) * ((f.colNext 50 - f.colCurr 50) - Felt.ofNat 27)) * ((f.colNext 50 - f.colCurr 50) - Felt.ofNat 81)) * ((f.colNext 50 - f.colCurr 50) - Felt.ofNat 243)) * ((f.colNext 50 - f.colCurr 50) - Felt.ofNat 729)) * ((f.colNext 50 - f.colCurr 50) - Felt.ofNat 2187)))
]

end MidenLean.AIR.Constraints.Symbolic.Range
