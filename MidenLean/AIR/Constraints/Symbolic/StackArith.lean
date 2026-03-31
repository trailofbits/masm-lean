import MidenLean.AIR.SymbolicFrame
set_option maxHeartbeats 8000000
/-! StackArith AIR constraints: 42 base + 0 ext. Auto-extracted. -/

namespace MidenLean.AIR.Constraints.Symbolic.StackArith

open MidenLean MidenLean.AIR

private def base_0_to_19 : List SymbolicConstraint := [
  -- StackArith.base[0]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 - (f.s 0 + f.s 1)))),
  -- StackArith.base[1]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 + f.s 0))),
  -- StackArith.base[2]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * (f.s' 0 - (f.s 0 * f.s 1)))),
  -- StackArith.base[3]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) * ((f.s' 0 * f.s 0) - 1))),
  -- StackArith.base[4]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * ((f.s' 0 - f.s 0) - 1))),
  -- StackArith.base[5]
  fun f => (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s 0 * (f.s 0 - 1))),
  -- StackArith.base[6]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * ((f.s 0 + f.s' 0) - 1))),
  -- StackArith.base[7]
  fun f => ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s 0 * (f.s 0 - 1))),
  -- StackArith.base[8]
  fun f => ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s 1 * (f.s 1 - 1))),
  -- StackArith.base[9]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 0 - (f.s 0 * f.s 1)))),
  -- StackArith.base[10]
  fun f => ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s 0 * (f.s 0 - 1))),
  -- StackArith.base[11]
  fun f => ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s 1 * (f.s 1 - 1))),
  -- StackArith.base[12]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 0 - ((f.s 0 + f.s 1) - (f.s 0 * f.s 1))))),
  -- StackArith.base[13]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * ((f.s 0 - f.s 1) * f.s' 0))),
  -- StackArith.base[14]
  fun f => (f.is_transition * ((((((f.colCurr 12 * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 0 - (1 - ((f.s 0 - f.s 1) * f.h 0))))),
  -- StackArith.base[15]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s 0 * f.s' 0))),
  -- StackArith.base[16]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 0 - (1 - (f.s 0 * f.h 0))))),
  -- StackArith.base[17]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * f.colCurr 7) * (f.s' 1 - (f.s 1 * f.s 1)))),
  -- StackArith.base[18]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * f.colCurr 7) * ((f.h 0 - 1) - ((f.s 1 - 1) * f.s' 0)))),
  -- StackArith.base[19]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * f.colCurr 7) * (f.s' 2 - (f.s 2 * f.h 0))))
]

private def base_20_to_39 : List SymbolicConstraint := [
  -- StackArith.base[20]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * f.colCurr 7) * ((f.s 3 - (f.s' 3 * Felt.ofNat 2)) - f.s' 0))),
  -- StackArith.base[21]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) * ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * f.colCurr 8) * f.colCurr 7) * (f.s' 0 * (f.s' 0 - 1)))),
  -- StackArith.base[22]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 0 - f.s 0))),
  -- StackArith.base[23]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 1 - f.s 1))),
  -- StackArith.base[24]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 2 - ((f.s 2 * f.s 0) + (Felt.ofNat 7 * (f.s 3 * f.s 1)))))),
  -- StackArith.base[25]
  fun f => (f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) * ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 3 - ((((f.s 2 + f.s 3) * (f.s 0 + f.s 1)) - (f.s 2 * f.s 0)) - (f.s 3 * f.s 1))))),
  -- StackArith.base[26]
  fun f => ((((((1 - f.colCurr 8) * ((1 - f.colCurr 9) * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) + (((1 - f.colCurr 8) * (f.colCurr 9 * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) + ((f.colCurr 8 * (f.colCurr 9 * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) * ((1 - (f.h 4 * (Felt.ofNat 4294967295 - ((f.h 3 * Felt.ofNat 65536) + f.h 2)))) * ((f.h 1 * Felt.ofNat 65536) + f.h 0))),
  -- StackArith.base[27]
  fun f => (f.is_transition * ((((((((1 - f.colCurr 8) * ((1 - f.colCurr 9) * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) + (((1 - f.colCurr 8) * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) + (((1 - f.colCurr 8) * (f.colCurr 9 * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) + (((1 - f.colCurr 8) * (f.colCurr 9 * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) + ((f.colCurr 8 * (f.colCurr 9 * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) * (f.s' 0 - ((f.h 1 * Felt.ofNat 65536) + f.h 0)))),
  -- StackArith.base[28]
  fun f => (f.is_transition * ((((((((1 - f.colCurr 8) * ((1 - f.colCurr 9) * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) + (((1 - f.colCurr 8) * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) + (((1 - f.colCurr 8) * (f.colCurr 9 * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) + (((1 - f.colCurr 8) * (f.colCurr 9 * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) + ((f.colCurr 8 * (f.colCurr 9 * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) * (f.s' 1 - ((f.h 3 * Felt.ofNat 65536) + f.h 2)))),
  -- StackArith.base[29]
  fun f => ((((1 - f.colCurr 8) * ((1 - f.colCurr 9) * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (f.s 0 - ((f.h 3 * Felt.ofNat 281474976710656) + ((f.h 2 * Felt.ofNat 4294967296) + ((f.h 1 * Felt.ofNat 65536) + f.h 0))))),
  -- StackArith.base[30]
  fun f => ((((1 - f.colCurr 8) * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * ((f.s 0 + f.s 1) - ((f.h 2 * Felt.ofNat 4294967296) + ((f.h 1 * Felt.ofNat 65536) + f.h 0)))),
  -- StackArith.base[31]
  fun f => ((((1 - f.colCurr 8) * (f.colCurr 9 * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (((f.s 0 + f.s 1) + f.s 2) - ((f.h 2 * Felt.ofNat 4294967296) + ((f.h 1 * Felt.ofNat 65536) + f.h 0)))),
  -- StackArith.base[32]
  fun f => (f.is_transition * (((f.colCurr 8 * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (f.s 1 - ((f.s 0 + f.s' 1) - (f.s' 0 * Felt.ofNat 4294967296))))),
  -- StackArith.base[33]
  fun f => (f.is_transition * (((f.colCurr 8 * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (f.s' 0 * (f.s' 0 - 1)))),
  -- StackArith.base[34]
  fun f => (f.is_transition * (((f.colCurr 8 * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (f.s' 1 - ((f.h 1 * Felt.ofNat 65536) + f.h 0)))),
  -- StackArith.base[35]
  fun f => ((((1 - f.colCurr 8) * (f.colCurr 9 * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * ((f.s 0 * f.s 1) - ((f.h 3 * Felt.ofNat 281474976710656) + ((f.h 2 * Felt.ofNat 4294967296) + ((f.h 1 * Felt.ofNat 65536) + f.h 0))))),
  -- StackArith.base[36]
  fun f => (((f.colCurr 8 * (f.colCurr 9 * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (((f.s 0 * f.s 1) + f.s 2) - ((f.h 3 * Felt.ofNat 281474976710656) + ((f.h 2 * Felt.ofNat 4294967296) + ((f.h 1 * Felt.ofNat 65536) + f.h 0))))),
  -- StackArith.base[37]
  fun f => (f.is_transition * (((f.colCurr 8 * (f.colCurr 9 * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (f.s 1 - ((f.s 0 * f.s' 1) + f.s' 0)))),
  -- StackArith.base[38]
  fun f => (f.is_transition * (((f.colCurr 8 * (f.colCurr 9 * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * ((f.s 1 - f.s' 1) - ((f.h 1 * Felt.ofNat 65536) + f.h 0)))),
  -- StackArith.base[39]
  fun f => (f.is_transition * (((f.colCurr 8 * (f.colCurr 9 * (1 - f.colCurr 10))) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * ((f.s 0 - f.s' 0) - (((f.h 3 * Felt.ofNat 65536) + f.h 2) + 1))))
]

private def base_40_to_41 : List SymbolicConstraint := [
  -- StackArith.base[40]
  fun f => (f.is_transition * (((f.colCurr 8 * ((1 - f.colCurr 9) * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (f.s' 0 - ((f.h 3 * Felt.ofNat 65536) + f.h 2)))),
  -- StackArith.base[41]
  fun f => (f.is_transition * (((f.colCurr 8 * ((1 - f.colCurr 9) * f.colCurr 10)) * ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) * (f.s' 1 - ((f.h 1 * Felt.ofNat 65536) + f.h 0))))
]

def base : List SymbolicConstraint :=
  base_0_to_19 ++ base_20_to_39 ++ base_40_to_41

/-- Public alias for the extracted `ADD` base constraint (`base[0]`). -/
def add : SymbolicConstraint := base_0_to_19[0]

@[simp] theorem add_apply (f : SymbolicFrame) :
    add f =
      f.is_transition *
        ((((((f.colCurr 12 * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          (1 - f.colCurr 9)) * f.colCurr 8) * (1 - f.colCurr 7)) *
          (f.s' 0 - (f.s 0 + f.s 1))) := by
  rfl

/-- Public alias for the extracted `NEG` base constraint (`base[1]`). -/
def neg : SymbolicConstraint := base_0_to_19[1]

@[simp] theorem neg_apply (f : SymbolicFrame) :
    neg f =
      f.is_transition *
        (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          (1 - f.colCurr 9)) * f.colCurr 8) * (1 - f.colCurr 7)) *
          (f.s' 0 + f.s 0)) := by
  rfl

/-- Public alias for the extracted `MUL` base constraint (`base[2]`). -/
def mul : SymbolicConstraint := base_0_to_19[2]

@[simp] theorem mul_apply (f : SymbolicFrame) :
    mul f =
      f.is_transition *
        ((((((f.colCurr 12 * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) *
          (f.s' 0 - (f.s 0 * f.s 1))) := by
  rfl

/-- Public alias for the extracted `INV` base constraint (`base[3]`). -/
def inv : SymbolicConstraint := base_0_to_19[3]

@[simp] theorem inv_apply (f : SymbolicFrame) :
    inv f =
      f.is_transition *
        (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          (1 - f.colCurr 9)) * f.colCurr 8) * f.colCurr 7) *
          ((f.s' 0 * f.s 0) - 1)) := by
  rfl

/-- Public alias for the extracted `INCR` base constraint (`base[4]`). -/
def incr : SymbolicConstraint := base_0_to_19[4]

@[simp] theorem incr_apply (f : SymbolicFrame) :
    incr f =
      f.is_transition *
        (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) *
          ((f.s' 0 - f.s 0) - 1)) := by
  rfl

/-- Public alias for extracted `NOT` binaryity (`base[5]`). -/
def notBinary : SymbolicConstraint := base_0_to_19[5]

@[simp] theorem notBinary_apply (f : SymbolicFrame) :
    notBinary f =
      (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) *
          (f.s 0 * (f.s 0 - 1))) := by
  rfl

/-- Public alias for extracted `NOT` value relation (`base[6]`). -/
def notValue : SymbolicConstraint := base_0_to_19[6]

@[simp] theorem notValue_apply (f : SymbolicFrame) :
    notValue f =
      f.is_transition *
        (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) *
          ((f.s 0 + f.s' 0) - 1)) := by
  rfl

/-- Public alias for extracted `AND` binaryity on `s0` (`base[7]`). -/
def andS0Binary : SymbolicConstraint := base_0_to_19[7]

@[simp] theorem andS0Binary_apply (f : SymbolicFrame) :
    andS0Binary f =
      ((((((f.colCurr 12 * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) *
          (f.s 0 * (f.s 0 - 1))) := by
  rfl

/-- Public alias for extracted `AND` binaryity on `s1` (`base[8]`). -/
def andS1Binary : SymbolicConstraint := base_0_to_19[8]

@[simp] theorem andS1Binary_apply (f : SymbolicFrame) :
    andS1Binary f =
      ((((((f.colCurr 12 * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) *
          (f.s 1 * (f.s 1 - 1))) := by
  rfl

/-- Public alias for extracted `AND` value relation (`base[9]`). -/
def andValue : SymbolicConstraint := base_0_to_19[9]

@[simp] theorem andValue_apply (f : SymbolicFrame) :
    andValue f =
      f.is_transition *
        ((((((f.colCurr 12 * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          f.colCurr 9) * (1 - f.colCurr 8)) * (1 - f.colCurr 7)) *
          (f.s' 0 - (f.s 0 * f.s 1))) := by
  rfl

/-- Public alias for extracted `OR` binaryity on `s0` (`base[10]`). -/
def orS0Binary : SymbolicConstraint := base_0_to_19[10]

@[simp] theorem orS0Binary_apply (f : SymbolicFrame) :
    orS0Binary f =
      ((((((f.colCurr 12 * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) *
          (f.s 0 * (f.s 0 - 1))) := by
  rfl

/-- Public alias for extracted `OR` binaryity on `s1` (`base[11]`). -/
def orS1Binary : SymbolicConstraint := base_0_to_19[11]

@[simp] theorem orS1Binary_apply (f : SymbolicFrame) :
    orS1Binary f =
      ((((((f.colCurr 12 * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) *
          (f.s 1 * (f.s 1 - 1))) := by
  rfl

/-- Public alias for extracted `OR` value relation (`base[12]`). -/
def orValue : SymbolicConstraint := base_0_to_19[12]

@[simp] theorem orValue_apply (f : SymbolicFrame) :
    orValue f =
      f.is_transition *
        ((((((f.colCurr 12 * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          f.colCurr 9) * (1 - f.colCurr 8)) * f.colCurr 7) *
          (f.s' 0 - ((f.s 0 + f.s 1) - (f.s 0 * f.s 1)))) := by
  rfl

/-- Public alias for extracted `EQ` zero-product relation (`base[13]`). -/
def eqZeroProduct : SymbolicConstraint := base_0_to_19[13]

@[simp] theorem eqZeroProduct_apply (f : SymbolicFrame) :
    eqZeroProduct f =
      f.is_transition *
        ((((((f.colCurr 12 * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) *
          ((f.s 0 - f.s 1) * f.s' 0)) := by
  rfl

/-- Public alias for extracted `EQ` value relation (`base[14]`). -/
def eqValue : SymbolicConstraint := base_0_to_19[14]

@[simp] theorem eqValue_apply (f : SymbolicFrame) :
    eqValue f =
      f.is_transition *
        ((((((f.colCurr 12 * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) *
          (f.s' 0 - (1 - ((f.s 0 - f.s 1) * f.h 0)))) := by
  rfl

/-- Public alias for extracted `EQZ` zero-product relation (`base[15]`). -/
def eqzZeroProduct : SymbolicConstraint := base_0_to_19[15]

@[simp] theorem eqzZeroProduct_apply (f : SymbolicFrame) :
    eqzZeroProduct f =
      f.is_transition *
        (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) *
          (f.s 0 * f.s' 0)) := by
  rfl

/-- Public alias for extracted `EQZ` value relation (`base[16]`). -/
def eqzValue : SymbolicConstraint := base_0_to_19[16]

@[simp] theorem eqzValue_apply (f : SymbolicFrame) :
    eqzValue f =
      f.is_transition *
        (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * (1 - f.colCurr 10))) *
          (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) *
          (f.s' 0 - (1 - (f.s 0 * f.h 0)))) := by
  rfl

/-- Public alias for extracted `EXPACC` exp-square relation (`base[17]`). -/
def expaccExpSquare : SymbolicConstraint := base_0_to_19[17]

@[simp] theorem expaccExpSquare_apply (f : SymbolicFrame) :
    expaccExpSquare f =
      f.is_transition *
        (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * f.colCurr 10)) *
          f.colCurr 9) * f.colCurr 8) * f.colCurr 7) *
          (f.s' 1 - (f.s 1 * f.s 1))) := by
  rfl

/-- Public alias for extracted `EXPACC` helper relation (`base[18]`). -/
def expaccExpVal : SymbolicConstraint := base_0_to_19[18]

@[simp] theorem expaccExpVal_apply (f : SymbolicFrame) :
    expaccExpVal f =
      f.is_transition *
        (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * f.colCurr 10)) *
          f.colCurr 9) * f.colCurr 8) * f.colCurr 7) *
          ((f.h 0 - 1) - ((f.s 1 - 1) * f.s' 0))) := by
  rfl

/-- Public alias for extracted `EXPACC` accumulator update (`base[19]`). -/
def expaccAccUpdate : SymbolicConstraint := base_0_to_19[19]

@[simp] theorem expaccAccUpdate_apply (f : SymbolicFrame) :
    expaccAccUpdate f =
      f.is_transition *
        (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * f.colCurr 10)) *
          f.colCurr 9) * f.colCurr 8) * f.colCurr 7) *
          (f.s' 2 - (f.s 2 * f.h 0))) := by
  rfl

/-- Public alias for extracted `EXPACC` exponent-shift relation (`base[20]`). -/
def expaccExpShift : SymbolicConstraint := base_20_to_39[0]

@[simp] theorem expaccExpShift_apply (f : SymbolicFrame) :
    expaccExpShift f =
      f.is_transition *
        (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * f.colCurr 10)) *
          f.colCurr 9) * f.colCurr 8) * f.colCurr 7) *
          ((f.s 3 - (f.s' 3 * Felt.ofNat 2)) - f.s' 0)) := by
  rfl

/-- Public alias for extracted `EXPACC` bit binaryity relation (`base[21]`). -/
def expaccBitBinary : SymbolicConstraint := base_20_to_39[1]

@[simp] theorem expaccBitBinary_apply (f : SymbolicFrame) :
    expaccBitBinary f =
      f.is_transition *
        (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) *
          ((1 - f.colCurr 13) * f.colCurr 10)) *
          f.colCurr 9) * f.colCurr 8) * f.colCurr 7) *
          (f.s' 0 * (f.s' 0 - 1))) := by
  rfl

/-- Public alias for extracted `EXT2MUL` `d0` relation (`base[22]`). -/
def ext2mulD0 : SymbolicConstraint := base_20_to_39[2]

@[simp] theorem ext2mulD0_apply (f : SymbolicFrame) :
    ext2mulD0 f =
      f.is_transition *
        (((((((1 - f.colCurr 12) * f.colCurr 11) *
          ((1 - f.colCurr 13) * f.colCurr 10)) *
          (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) *
          (f.s' 0 - f.s 0)) := by
  rfl

/-- Public alias for extracted `EXT2MUL` `d1` relation (`base[23]`). -/
def ext2mulD1 : SymbolicConstraint := base_20_to_39[3]

@[simp] theorem ext2mulD1_apply (f : SymbolicFrame) :
    ext2mulD1 f =
      f.is_transition *
        (((((((1 - f.colCurr 12) * f.colCurr 11) *
          ((1 - f.colCurr 13) * f.colCurr 10)) *
          (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) *
          (f.s' 1 - f.s 1)) := by
  rfl

/-- Public alias for extracted `EXT2MUL` `c0` relation (`base[24]`). -/
def ext2mulC0 : SymbolicConstraint := base_20_to_39[4]

@[simp] theorem ext2mulC0_apply (f : SymbolicFrame) :
    ext2mulC0 f =
      f.is_transition *
        (((((((1 - f.colCurr 12) * f.colCurr 11) *
          ((1 - f.colCurr 13) * f.colCurr 10)) *
          (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) *
          (f.s' 2 - ((f.s 2 * f.s 0) + (Felt.ofNat 7 * (f.s 3 * f.s 1))))) := by
  rfl

/-- Public alias for extracted `EXT2MUL` `c1` relation (`base[25]`). -/
def ext2mulC1 : SymbolicConstraint := base_20_to_39[5]

@[simp] theorem ext2mulC1_apply (f : SymbolicFrame) :
    ext2mulC1 f =
      f.is_transition *
        (((((((1 - f.colCurr 12) * f.colCurr 11) *
          ((1 - f.colCurr 13) * f.colCurr 10)) *
          (1 - f.colCurr 9)) * (1 - f.colCurr 8)) * f.colCurr 7) *
          (f.s' 3 - ((((f.s 2 + f.s 3) * (f.s 0 + f.s 1)) - (f.s 2 * f.s 0)) - (f.s 3 * f.s 1)))) := by
  rfl

/-- Public alias for extracted grouped `u32` validity relation (`base[26]`). -/
def u32SplitMulMaddValidity : SymbolicConstraint := base_20_to_39[6]

@[simp] theorem u32SplitMulMaddValidity_apply (f : SymbolicFrame) :
    u32SplitMulMaddValidity f =
      ((((((1 - f.colCurr 8) * ((1 - f.colCurr 9) * f.colCurr 10)) *
          ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) +
          (((1 - f.colCurr 8) * (f.colCurr 9 * (1 - f.colCurr 10))) *
            ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) +
          ((f.colCurr 8 * (f.colCurr 9 * f.colCurr 10)) *
            ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) *
        ((1 - (f.h 4 * (Felt.ofNat 4294967295 - ((f.h 3 * Felt.ofNat 65536) + f.h 2)))) *
          ((f.h 1 * Felt.ofNat 65536) + f.h 0))) := by
  rfl

/-- Public alias for extracted grouped `u32` output-low relation (`base[27]`). -/
def u32TwoOutputsLo : SymbolicConstraint := base_20_to_39[7]

@[simp] theorem u32TwoOutputsLo_apply (f : SymbolicFrame) :
    u32TwoOutputsLo f =
      f.is_transition *
        ((((((((1 - f.colCurr 8) * ((1 - f.colCurr 9) * f.colCurr 10)) *
            ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) +
            (((1 - f.colCurr 8) * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) *
              ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) +
            (((1 - f.colCurr 8) * (f.colCurr 9 * f.colCurr 10)) *
              ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) +
            (((1 - f.colCurr 8) * (f.colCurr 9 * (1 - f.colCurr 10))) *
              ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) +
            ((f.colCurr 8 * (f.colCurr 9 * f.colCurr 10)) *
              ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) *
          (f.s' 0 - ((f.h 1 * Felt.ofNat 65536) + f.h 0))) := by
  rfl

/-- Public alias for extracted grouped `u32` output-high relation (`base[28]`). -/
def u32TwoOutputsHi : SymbolicConstraint := base_20_to_39[8]

@[simp] theorem u32TwoOutputsHi_apply (f : SymbolicFrame) :
    u32TwoOutputsHi f =
      f.is_transition *
        ((((((((1 - f.colCurr 8) * ((1 - f.colCurr 9) * f.colCurr 10)) *
            ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) +
            (((1 - f.colCurr 8) * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) *
              ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) +
            (((1 - f.colCurr 8) * (f.colCurr 9 * f.colCurr 10)) *
              ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) +
            (((1 - f.colCurr 8) * (f.colCurr 9 * (1 - f.colCurr 10))) *
              ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) +
            ((f.colCurr 8 * (f.colCurr 9 * f.colCurr 10)) *
              ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)))) *
          (f.s' 1 - ((f.h 3 * Felt.ofNat 65536) + f.h 2))) := by
  rfl

/-- Public alias for extracted `U32SPLIT` input relation (`base[29]`). -/
def u32SplitInput : SymbolicConstraint := base_20_to_39[9]

@[simp] theorem u32SplitInput_apply (f : SymbolicFrame) :
    u32SplitInput f =
      ((((1 - f.colCurr 8) * ((1 - f.colCurr 9) * f.colCurr 10)) *
          ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) *
        (f.s 0 - ((f.h 3 * Felt.ofNat 281474976710656) +
          ((f.h 2 * Felt.ofNat 4294967296) + ((f.h 1 * Felt.ofNat 65536) + f.h 0))))) := by
  rfl

/-- Public alias for extracted `U32ADD` input relation (`base[30]`). -/
def u32AddInput : SymbolicConstraint := base_20_to_39[10]

@[simp] theorem u32AddInput_apply (f : SymbolicFrame) :
    u32AddInput f =
      ((((1 - f.colCurr 8) * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) *
          ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) *
        ((f.s 0 + f.s 1) - ((f.h 2 * Felt.ofNat 4294967296) +
          ((f.h 1 * Felt.ofNat 65536) + f.h 0)))) := by
  rfl

/-- Public alias for extracted `U32ADD3` input relation (`base[31]`). -/
def u32Add3Input : SymbolicConstraint := base_20_to_39[11]

@[simp] theorem u32Add3Input_apply (f : SymbolicFrame) :
    u32Add3Input f =
    ((((1 - f.colCurr 8) * (f.colCurr 9 * f.colCurr 10)) *
        ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) *
        (((f.s 0 + f.s 1) + f.s 2) - ((f.h 2 * Felt.ofNat 4294967296) +
          ((f.h 1 * Felt.ofNat 65536) + f.h 0)))) := by
  rfl

/-- Public alias for extracted `U32SUB` difference relation (`base[32]`). -/
def u32SubDiff : SymbolicConstraint := base_20_to_39[12]

@[simp] theorem u32SubDiff_apply (f : SymbolicFrame) :
    u32SubDiff f =
      f.is_transition *
        (((f.colCurr 8 * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) *
          ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) *
          (f.s 1 - ((f.s 0 + f.s' 1) - (f.s' 0 * Felt.ofNat 4294967296)))) := by
  rfl

/-- Public alias for extracted `U32SUB` borrow binaryity (`base[33]`). -/
def u32SubBorrowBinary : SymbolicConstraint := base_20_to_39[13]

@[simp] theorem u32SubBorrowBinary_apply (f : SymbolicFrame) :
    u32SubBorrowBinary f =
      f.is_transition *
        (((f.colCurr 8 * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) *
          ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) *
          (f.s' 0 * (f.s' 0 - 1))) := by
  rfl

/-- Public alias for extracted `U32SUB` low output relation (`base[34]`). -/
def u32SubLow : SymbolicConstraint := base_20_to_39[14]

@[simp] theorem u32SubLow_apply (f : SymbolicFrame) :
    u32SubLow f =
      f.is_transition *
        (((f.colCurr 8 * ((1 - f.colCurr 9) * (1 - f.colCurr 10))) *
          ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) *
          (f.s' 1 - ((f.h 1 * Felt.ofNat 65536) + f.h 0))) := by
  rfl

-- Public alias for extracted `U32MUL` relation (`base[35]`). 
def u32Mul : SymbolicConstraint := base_20_to_39[15]

@[simp] theorem u32Mul_apply (f : SymbolicFrame) :
    u32Mul f =
      ((((1 - f.colCurr 8) * (f.colCurr 9 * (1 - f.colCurr 10))) *
          ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) *
        ((f.s 0 * f.s 1) - ((f.h 3 * Felt.ofNat 281474976710656) +
          ((f.h 2 * Felt.ofNat 4294967296) + ((f.h 1 * Felt.ofNat 65536) + f.h 0))))) := by
  rfl

-- Public alias for extracted `U32MADD` relation (`base[36]`). -/
def u32Madd : SymbolicConstraint := base_20_to_39[16]

@[simp] theorem u32Madd_apply (f : SymbolicFrame) :
    u32Madd f =
      (((f.colCurr 8 * (f.colCurr 9 * f.colCurr 10)) *
          ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) *
        (((f.s 0 * f.s 1) + f.s 2) - ((f.h 3 * Felt.ofNat 281474976710656) +
          ((f.h 2 * Felt.ofNat 4294967296) + ((f.h 1 * Felt.ofNat 65536) + f.h 0))))) := by
  rfl


/-- Public alias for extracted `U32DIV` dividend relation (`base[37]`). -/
def u32DivDividend : SymbolicConstraint := base_20_to_39[17]

@[simp] theorem u32DivDividend_apply (f : SymbolicFrame) :
    u32DivDividend f =
      (f.colCurr 8 * (f.colCurr 9 * (1 - f.colCurr 10)) *
        ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) *
        (f.s 1 - ((f.s 0 * f.s' 1) + f.s' 0)) := by
  rfl

/-- Public alias for extracted `U32DIV` remainder-low relation (`base[38]`). -/
def u32DivLow : SymbolicConstraint := base_20_to_39[18]

@[simp] theorem u32DivLow_apply (f : SymbolicFrame) :
    u32DivLow f =
      (f.colCurr 8 * (f.colCurr 9 * (1 - f.colCurr 10)) *
        ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) *
        ((f.s 1 - f.s' 1) - ((f.h 1 * Felt.ofNat 65536) + f.h 0)) := by
  rfl

/-- Public alias for extracted `U32DIV` remainder-high relation (`base[39]`). -/
def u32DivHigh : SymbolicConstraint := base_20_to_39[19]

@[simp] theorem u32DivHigh_apply (f : SymbolicFrame) :
    u32DivHigh f =
      (f.colCurr 8 * (f.colCurr 9 * (1 - f.colCurr 10)) *
        ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) *
        ((f.s 0 - f.s' 0) - (((f.h 3 * Felt.ofNat 65536) + f.h 2) + 1)) := by
  rfl

/-- Public alias for extracted `U32ASSERT2` high-output relation (`base[40]`). -/
def u32Assert2Hi : SymbolicConstraint := base_40_to_41[0]

@[simp] theorem u32Assert2Hi_apply (f : SymbolicFrame) :
    u32Assert2Hi f =
      f.is_transition *
        (((f.colCurr 8 * ((1 - f.colCurr 9) * f.colCurr 10)) *
          ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) *
          (f.s' 0 - ((f.h 3 * Felt.ofNat 65536) + f.h 2))) := by
  rfl

/-- Public alias for extracted `U32ASSERT2` low-output relation (`base[41]`). -/
def u32Assert2Lo : SymbolicConstraint := base_40_to_41[1]

@[simp] theorem u32Assert2Lo_apply (f : SymbolicFrame) :
    u32Assert2Lo f =
      f.is_transition *
        (((f.colCurr 8 * ((1 - f.colCurr 9) * f.colCurr 10)) *
          ((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11))) *
          (f.s' 1 - ((f.h 1 * Felt.ofNat 65536) + f.h 0))) := by
  rfl

end MidenLean.AIR.Constraints.Symbolic.StackArith
