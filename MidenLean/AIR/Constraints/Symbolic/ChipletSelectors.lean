import MidenLean.AIR.SymbolicFrame
set_option maxHeartbeats 8000000
/-! ChipletSelectors AIR constraints: 10 base + 0 ext. Auto-extracted. -/

namespace MidenLean.AIR.Constraints.Symbolic.ChipletSelectors

open MidenLean MidenLean.AIR

def base : List SymbolicConstraint := [
  -- ChipletSelectors.base[0]
  fun f => (f.colCurr 51 * (f.colCurr 51 - 1)),
  -- ChipletSelectors.base[1]
  fun f => (f.colCurr 51 * (f.colCurr 52 * (f.colCurr 52 - 1))),
  -- ChipletSelectors.base[2]
  fun f => (f.colCurr 51 * (f.colCurr 52 * (f.colCurr 53 * (f.colCurr 53 - 1)))),
  -- ChipletSelectors.base[3]
  fun f => (f.colCurr 51 * (f.colCurr 52 * (f.colCurr 53 * (f.colCurr 54 * (f.colCurr 54 - 1))))),
  -- ChipletSelectors.base[4]
  fun f => (f.colCurr 51 * (f.colCurr 52 * (f.colCurr 53 * (f.colCurr 54 * (f.colCurr 55 * (f.colCurr 55 - 1)))))),
  -- ChipletSelectors.base[5]
  fun f => (f.is_transition * (f.colCurr 51 * (f.colNext 51 - f.colCurr 51))),
  -- ChipletSelectors.base[6]
  fun f => (f.is_transition * (f.colCurr 51 * (f.colCurr 52 * (f.colNext 52 - f.colCurr 52)))),
  -- ChipletSelectors.base[7]
  fun f => (f.is_transition * (f.colCurr 51 * (f.colCurr 52 * (f.colCurr 53 * (f.colNext 53 - f.colCurr 53))))),
  -- ChipletSelectors.base[8]
  fun f => (f.is_transition * (f.colCurr 51 * (f.colCurr 52 * (f.colCurr 53 * (f.colCurr 54 * (f.colNext 54 - f.colCurr 54)))))),
  -- ChipletSelectors.base[9]
  fun f => (f.is_transition * (f.colCurr 51 * (f.colCurr 52 * (f.colCurr 53 * (f.colCurr 54 * (f.colCurr 55 * (f.colNext 55 - f.colCurr 55)))))))
]

end MidenLean.AIR.Constraints.Symbolic.ChipletSelectors
