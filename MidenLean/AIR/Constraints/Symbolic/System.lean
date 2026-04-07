import MidenLean.AIR.SymbolicFrame
/-! System AIR constraints: 13 base + 0 ext. Auto-extracted. -/

namespace MidenLean.AIR.Constraints.Symbolic.System

open MidenLean MidenLean.AIR

def base : List SymbolicConstraint := [
  -- System.base[0]
  fun f => (f.is_first_row * f.clk),
  -- System.base[1]
  fun f => (f.is_transition * (f.clk' - (f.clk + 1))),
  -- System.base[2]
  fun f => (f.is_transition * ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * (f.colCurr 13 * f.colCurr 12))) + ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * (f.colCurr 10 * (f.colCurr 13 * (1 - f.colCurr 12) * f.colCurr 11)))) * (f.ctx' - (f.clk + 1)))),
  -- System.base[3]
  fun f => (f.is_transition * ((((1 - f.colCurr 9) * f.colCurr 10) * ((1 - f.colCurr 11) * (f.colCurr 13 * f.colCurr 12))) * f.ctx')),
  -- System.base[4]
  fun f => (f.is_transition * ((1 - (((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * (f.colCurr 13 * f.colCurr 12))) + (((1 - f.colCurr 9) * f.colCurr 10) * ((1 - f.colCurr 11) * (f.colCurr 13 * f.colCurr 12)))) + ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * (f.colCurr 10 * (f.colCurr 13 * (1 - f.colCurr 12) * f.colCurr 11)))) + (((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * (f.colCurr 13 * f.colCurr 12))))) * (f.ctx' - f.ctx))),
  -- System.base[5]
  fun f => (f.is_transition * ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * (f.colCurr 13 * f.colCurr 12))) + ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * (f.colCurr 10 * (f.colCurr 13 * (1 - f.colCurr 12) * f.colCurr 11)))) * (f.colNext 2 - f.colCurr 14))),
  -- System.base[6]
  fun f => (f.is_transition * ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * (f.colCurr 13 * f.colCurr 12))) + ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * (f.colCurr 10 * (f.colCurr 13 * (1 - f.colCurr 12) * f.colCurr 11)))) * (f.colNext 3 - f.colCurr 15))),
  -- System.base[7]
  fun f => (f.is_transition * ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * (f.colCurr 13 * f.colCurr 12))) + ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * (f.colCurr 10 * (f.colCurr 13 * (1 - f.colCurr 12) * f.colCurr 11)))) * (f.colNext 4 - f.h 0))),
  -- System.base[8]
  fun f => (f.is_transition * ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * (f.colCurr 13 * f.colCurr 12))) + ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * (f.colCurr 10 * (f.colCurr 13 * (1 - f.colCurr 12) * f.colCurr 11)))) * (f.colNext 5 - f.h 1))),
  -- System.base[9]
  fun f => (f.is_transition * ((1 - ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * (f.colCurr 13 * f.colCurr 12))) + ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * (f.colCurr 10 * (f.colCurr 13 * (1 - f.colCurr 12) * f.colCurr 11)))) + (((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * (f.colCurr 13 * f.colCurr 12))))) * (f.colNext 2 - f.colCurr 2))),
  -- System.base[10]
  fun f => (f.is_transition * ((1 - ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * (f.colCurr 13 * f.colCurr 12))) + ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * (f.colCurr 10 * (f.colCurr 13 * (1 - f.colCurr 12) * f.colCurr 11)))) + (((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * (f.colCurr 13 * f.colCurr 12))))) * (f.colNext 3 - f.colCurr 3))),
  -- System.base[11]
  fun f => (f.is_transition * ((1 - ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * (f.colCurr 13 * f.colCurr 12))) + ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * (f.colCurr 10 * (f.colCurr 13 * (1 - f.colCurr 12) * f.colCurr 11)))) + (((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * (f.colCurr 13 * f.colCurr 12))))) * (f.colNext 4 - f.colCurr 4))),
  -- System.base[12]
  fun f => (f.is_transition * ((1 - ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * (f.colCurr 13 * f.colCurr 12))) + ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * (f.colCurr 10 * (f.colCurr 13 * (1 - f.colCurr 12) * f.colCurr 11)))) + (((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * (f.colCurr 13 * f.colCurr 12))))) * (f.colNext 5 - f.colCurr 5)))
]

end MidenLean.AIR.Constraints.Symbolic.System
