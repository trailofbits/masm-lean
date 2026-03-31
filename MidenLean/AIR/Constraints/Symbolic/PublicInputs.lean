import MidenLean.AIR.SymbolicFrame
set_option maxHeartbeats 8000000
/-! PublicInputs AIR constraints: 32 base + 0 ext. Auto-extracted. -/

namespace MidenLean.AIR.Constraints.Symbolic.PublicInputs

open MidenLean MidenLean.AIR

private def base_0_to_19 : List SymbolicConstraint := [
  -- PublicInputs.base[0]
  fun f => (f.is_first_row * (f.s 0 - f.publicValue 4)),
  -- PublicInputs.base[1]
  fun f => (f.is_first_row * (f.s 1 - f.publicValue 5)),
  -- PublicInputs.base[2]
  fun f => (f.is_first_row * (f.s 2 - f.publicValue 6)),
  -- PublicInputs.base[3]
  fun f => (f.is_first_row * (f.s 3 - f.publicValue 7)),
  -- PublicInputs.base[4]
  fun f => (f.is_first_row * (f.s 4 - f.publicValue 8)),
  -- PublicInputs.base[5]
  fun f => (f.is_first_row * (f.s 5 - f.publicValue 9)),
  -- PublicInputs.base[6]
  fun f => (f.is_first_row * (f.s 6 - f.publicValue 10)),
  -- PublicInputs.base[7]
  fun f => (f.is_first_row * (f.s 7 - f.publicValue 11)),
  -- PublicInputs.base[8]
  fun f => (f.is_first_row * (f.s 8 - f.publicValue 12)),
  -- PublicInputs.base[9]
  fun f => (f.is_first_row * (f.s 9 - f.publicValue 13)),
  -- PublicInputs.base[10]
  fun f => (f.is_first_row * (f.s 10 - f.publicValue 14)),
  -- PublicInputs.base[11]
  fun f => (f.is_first_row * (f.s 11 - f.publicValue 15)),
  -- PublicInputs.base[12]
  fun f => (f.is_first_row * (f.s 12 - f.publicValue 16)),
  -- PublicInputs.base[13]
  fun f => (f.is_first_row * (f.s 13 - f.publicValue 17)),
  -- PublicInputs.base[14]
  fun f => (f.is_first_row * (f.s 14 - f.publicValue 18)),
  -- PublicInputs.base[15]
  fun f => (f.is_first_row * (f.s 15 - f.publicValue 19)),
  -- PublicInputs.base[16]
  fun f => (f.is_last_row * (f.s 0 - f.publicValue 20)),
  -- PublicInputs.base[17]
  fun f => (f.is_last_row * (f.s 1 - f.publicValue 21)),
  -- PublicInputs.base[18]
  fun f => (f.is_last_row * (f.s 2 - f.publicValue 22)),
  -- PublicInputs.base[19]
  fun f => (f.is_last_row * (f.s 3 - f.publicValue 23))
]

private def base_20_to_31 : List SymbolicConstraint := [
  -- PublicInputs.base[20]
  fun f => (f.is_last_row * (f.s 4 - f.publicValue 24)),
  -- PublicInputs.base[21]
  fun f => (f.is_last_row * (f.s 5 - f.publicValue 25)),
  -- PublicInputs.base[22]
  fun f => (f.is_last_row * (f.s 6 - f.publicValue 26)),
  -- PublicInputs.base[23]
  fun f => (f.is_last_row * (f.s 7 - f.publicValue 27)),
  -- PublicInputs.base[24]
  fun f => (f.is_last_row * (f.s 8 - f.publicValue 28)),
  -- PublicInputs.base[25]
  fun f => (f.is_last_row * (f.s 9 - f.publicValue 29)),
  -- PublicInputs.base[26]
  fun f => (f.is_last_row * (f.s 10 - f.publicValue 30)),
  -- PublicInputs.base[27]
  fun f => (f.is_last_row * (f.s 11 - f.publicValue 31)),
  -- PublicInputs.base[28]
  fun f => (f.is_last_row * (f.s 12 - f.publicValue 32)),
  -- PublicInputs.base[29]
  fun f => (f.is_last_row * (f.s 13 - f.publicValue 33)),
  -- PublicInputs.base[30]
  fun f => (f.is_last_row * (f.s 14 - f.publicValue 34)),
  -- PublicInputs.base[31]
  fun f => (f.is_last_row * (f.s 15 - f.publicValue 35))
]

def base : List SymbolicConstraint :=
  base_0_to_19 ++ base_20_to_31

end MidenLean.AIR.Constraints.Symbolic.PublicInputs
