import MidenLean.AIR.SymbolicFrame
set_option maxHeartbeats 8000000
/-! StackOps AIR constraints: 88 base + 0 ext. Auto-extracted. -/

namespace MidenLean.AIR.Constraints.Symbolic.StackOps

open MidenLean MidenLean.AIR

private def base_0_to_19 : List SymbolicConstraint := [
  -- StackOps.base[0]
  fun f => (f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * f.s' 0)),
  -- StackOps.base[1]
  fun f => (f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 0 - f.s 0))),
  -- StackOps.base[2]
  fun f => (f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 1))),
  -- StackOps.base[3]
  fun f => (f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * (f.s' 0 - f.s 2))),
  -- StackOps.base[4]
  fun f => (f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 3))),
  -- StackOps.base[5]
  fun f => (f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 0 - f.s 4))),
  -- StackOps.base[6]
  fun f => (f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 5))),
  -- StackOps.base[7]
  fun f => (f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * f.colCurr 8) * f.colCurr 7) * (f.s' 0 - f.s 6))),
  -- StackOps.base[8]
  fun f => (f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 7))),
  -- StackOps.base[9]
  fun f => (f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 0 - f.s 9))),
  -- StackOps.base[10]
  fun f => (f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 11))),
  -- StackOps.base[11]
  fun f => (f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * (f.s' 0 - f.s 13))),
  -- StackOps.base[12]
  fun f => (f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 15))),
  -- StackOps.base[13]
  fun f => (f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * f.colCurr 7) * (f.s' 0 - f.clk))),
  -- StackOps.base[14]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 1))),
  -- StackOps.base[15]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 1 - f.s 0))),
  -- StackOps.base[16]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 2))),
  -- StackOps.base[17]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 3))),
  -- StackOps.base[18]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 4))),
  -- StackOps.base[19]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 5)))
]

private def base_20_to_39 : List SymbolicConstraint := [
  -- StackOps.base[20]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 6))),
  -- StackOps.base[21]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 7))),
  -- StackOps.base[22]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 8))),
  -- StackOps.base[23]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * (f.s' 2 - f.s 0))),
  -- StackOps.base[24]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 3 - f.s 0))),
  -- StackOps.base[25]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 4 - f.s 0))),
  -- StackOps.base[26]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * (f.s' 5 - f.s 0))),
  -- StackOps.base[27]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 6 - f.s 0))),
  -- StackOps.base[28]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * f.colCurr 8) * f.colCurr 7) * (f.s' 7 - f.s 0))),
  -- StackOps.base[29]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * (f.s' 8 - f.s 0))),
  -- StackOps.base[30]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 4))),
  -- StackOps.base[31]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 1 - f.s 5))),
  -- StackOps.base[32]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 2 - f.s 6))),
  -- StackOps.base[33]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 3 - f.s 7))),
  -- StackOps.base[34]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 4 - f.s 0))),
  -- StackOps.base[35]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 5 - f.s 1))),
  -- StackOps.base[36]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 6 - f.s 2))),
  -- StackOps.base[37]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 7 - f.s 3))),
  -- StackOps.base[38]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 8))),
  -- StackOps.base[39]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 1 - f.s 9)))
]

private def base_40_to_59 : List SymbolicConstraint := [
  -- StackOps.base[40]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 2 - f.s 10))),
  -- StackOps.base[41]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 3 - f.s 11))),
  -- StackOps.base[42]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 8 - f.s 0))),
  -- StackOps.base[43]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 9 - f.s 1))),
  -- StackOps.base[44]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 10 - f.s 2))),
  -- StackOps.base[45]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 11 - f.s 3))),
  -- StackOps.base[46]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 0 - f.s 12))),
  -- StackOps.base[47]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 1 - f.s 13))),
  -- StackOps.base[48]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 2 - f.s 14))),
  -- StackOps.base[49]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 3 - f.s 15))),
  -- StackOps.base[50]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 12 - f.s 0))),
  -- StackOps.base[51]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 13 - f.s 1))),
  -- StackOps.base[52]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 14 - f.s 2))),
  -- StackOps.base[53]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 15 - f.s 3))),
  -- StackOps.base[54]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 8))),
  -- StackOps.base[55]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 1 - f.s 9))),
  -- StackOps.base[56]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 2 - f.s 10))),
  -- StackOps.base[57]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 3 - f.s 11))),
  -- StackOps.base[58]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 4 - f.s 12))),
  -- StackOps.base[59]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 5 - f.s 13)))
]

private def base_60_to_79 : List SymbolicConstraint := [
  -- StackOps.base[60]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 6 - f.s 14))),
  -- StackOps.base[61]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 7 - f.s 15))),
  -- StackOps.base[62]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 8 - f.s 0))),
  -- StackOps.base[63]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 9 - f.s 1))),
  -- StackOps.base[64]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 10 - f.s 2))),
  -- StackOps.base[65]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 11 - f.s 3))),
  -- StackOps.base[66]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 12 - f.s 4))),
  -- StackOps.base[67]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 13 - f.s 5))),
  -- StackOps.base[68]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 14 - f.s 6))),
  -- StackOps.base[69]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 15 - f.s 7))),
  -- StackOps.base[70]
  fun f => ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s 0 * (f.s 0 - 1))),
  -- StackOps.base[71]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 - ((f.s 0 * f.s 2) + ((1 - f.s 0) * f.s 1))))),
  -- StackOps.base[72]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 1 - ((f.s 0 * f.s 1) + ((1 - f.s 0) * f.s 2))))),
  -- StackOps.base[73]
  fun f => ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * (f.s 0 * (f.s 0 - 1))),
  -- StackOps.base[74]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * (f.s' 0 - ((f.s 0 * f.s 5) + ((1 - f.s 0) * f.s 1))))),
  -- StackOps.base[75]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * (f.s' 1 - ((f.s 0 * f.s 6) + ((1 - f.s 0) * f.s 2))))),
  -- StackOps.base[76]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * (f.s' 2 - ((f.s 0 * f.s 7) + ((1 - f.s 0) * f.s 3))))),
  -- StackOps.base[77]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * (f.s' 3 - ((f.s 0 * f.s 8) + ((1 - f.s 0) * f.s 4))))),
  -- StackOps.base[78]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * (f.s' 4 - ((f.s 0 * f.s 1) + ((1 - f.s 0) * f.s 5))))),
  -- StackOps.base[79]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * (f.s' 5 - ((f.s 0 * f.s 2) + ((1 - f.s 0) * f.s 6)))))
]

private def base_80_to_87 : List SymbolicConstraint := [
  -- StackOps.base[80]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * (f.s' 6 - ((f.s 0 * f.s 3) + ((1 - f.s 0) * f.s 7))))),
  -- StackOps.base[81]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * (f.s' 7 - ((f.s 0 * f.s 4) + ((1 - f.s 0) * f.s 8))))),
  -- StackOps.base[82]
  fun f => ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s 0 - 1)),
  -- StackOps.base[83]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 0 - f.colCurr 2))),
  -- StackOps.base[84]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 1 - f.colCurr 3))),
  -- StackOps.base[85]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 2 - f.colCurr 4))),
  -- StackOps.base[86]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 3 - f.colCurr 5))),
  -- StackOps.base[87]
  fun f => (f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 - f.b0)))
]

def base : List SymbolicConstraint :=
  base_0_to_19 ++ base_20_to_39 ++ base_40_to_59 ++ base_60_to_79 ++ base_80_to_87

end MidenLean.AIR.Constraints.Symbolic.StackOps
