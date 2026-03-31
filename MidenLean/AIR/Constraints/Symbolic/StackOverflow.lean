import MidenLean.AIR.SymbolicFrame
set_option maxHeartbeats 8000000
/-! StackOverflow AIR constraints: 8 base + 0 ext. Auto-extracted. -/

namespace MidenLean.AIR.Constraints.Symbolic.StackOverflow

open MidenLean MidenLean.AIR

def base : List SymbolicConstraint := [
  -- StackOverflow.base[0]
  fun f => (f.is_first_row * (f.b0 - Felt.ofNat 16)),
  -- StackOverflow.base[1]
  fun f => (f.is_last_row * (f.b0 - Felt.ofNat 16)),
  -- StackOverflow.base[2]
  fun f => (f.is_first_row * f.b1),
  -- StackOverflow.base[3]
  fun f => (f.is_last_row * f.b1),
  -- StackOverflow.base[4]
  fun f => (f.is_transition * (((((f.b0' - f.b0) * ((1 - ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29)) + ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * (f.colCurr 10 * f.colCurr 28))) + (((1 - f.colCurr 9) * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29)))) - ((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) * (f.h 4 + f.h 5)))) + (((((((((1 - f.colCurr 13) * f.colCurr 12) * (1 - f.colCurr 11)) + ((((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)) * f.colCurr 10) * f.colCurr 9)) + (((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28)) + (((f.colCurr 7 * (1 - f.colCurr 8)) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28)))) + ((f.colCurr 9 * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29))) + ((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) * f.h 3)) + ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28))) * ((f.b0 - Felt.ofNat 16) * f.h0_overflow))) - (((((1 - f.colCurr 13) * f.colCurr 12) * f.colCurr 11) + (((f.colCurr 7 * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28))) + (((1 - f.colCurr 8) * ((1 - f.colCurr 9) * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))))) + (((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29)) + ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * (f.colCurr 10 * f.colCurr 28))) + (((1 - f.colCurr 9) * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29))) * (f.b0' - Felt.ofNat 16)))),
  -- StackOverflow.base[5]
  fun f => ((1 - ((f.b0 - Felt.ofNat 16) * f.h0_overflow)) * (f.b0 - Felt.ofNat 16)),
  -- StackOverflow.base[6]
  fun f => (f.is_transition * ((f.b1' - f.clk) * (((((1 - f.colCurr 13) * f.colCurr 12) * f.colCurr 11) + (((f.colCurr 7 * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28))) + (((1 - f.colCurr 8) * ((1 - f.colCurr 9) * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))))),
  -- StackOverflow.base[7]
  fun f => (f.is_transition * (((1 - ((f.b0 - Felt.ofNat 16) * f.h0_overflow)) * ((((((((1 - f.colCurr 13) * f.colCurr 12) * (1 - f.colCurr 11)) + ((((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)) * f.colCurr 10) * f.colCurr 9)) + (((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28)) + (((f.colCurr 7 * (1 - f.colCurr 8)) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28)))) + ((f.colCurr 9 * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29))) + ((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) * f.h 3)) + ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)))) * f.s' 15))
]

end MidenLean.AIR.Constraints.Symbolic.StackOverflow
