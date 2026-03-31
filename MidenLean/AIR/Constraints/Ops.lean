import MidenLean.AIR.Frame
/-!
# AIR Constraints (Frame-based) - Ops Kernel

Canonical non-generated local kernel for operation-level constraints.

Definitions here mirror the currently runnable op constraints used in proofs/tests.
-/

namespace MidenLean.AIR.Constraints

open MidenLean MidenLean.AIR

/-- ASSERT: 1 constraint(s). -/
def assert_op : ConstraintSet := [
  -- [integrity]
  fun f => (f.s 0 - 1)
]

-- CALLER and CLK omitted: reference fn_hash/clk columns not in Frame.

/-- CSWAP: 3 constraint(s). -/
def cswap : ConstraintSet := [
  -- [integrity]
  fun f => (f.s 0 * (f.s 0 - 1)),
  -- [exact]
  fun f => (f.s' 0 - ((f.s 0 * f.s 2) + ((1 - f.s 0) * f.s 1))),
  -- [exact]
  fun f => (f.s' 1 - ((f.s 0 * f.s 1) + ((1 - f.s 0) * f.s 2)))
]

/-- CSWAPW: 9 constraint(s). -/
def cswapw : ConstraintSet := [
  -- [integrity]
  fun f => (f.s 0 * (f.s 0 - 1)),
  -- [exact]
  fun f => (f.s' 0 - ((f.s 0 * f.s 5) + ((1 - f.s 0) * f.s 1))),
  -- [exact]
  fun f => (f.s' 1 - ((f.s 0 * f.s 6) + ((1 - f.s 0) * f.s 2))),
  -- [exact]
  fun f => (f.s' 2 - ((f.s 0 * f.s 7) + ((1 - f.s 0) * f.s 3))),
  -- [exact]
  fun f => (f.s' 3 - ((f.s 0 * f.s 8) + ((1 - f.s 0) * f.s 4))),
  -- [exact]
  fun f => (f.s' 4 - ((f.s 0 * f.s 1) + ((1 - f.s 0) * f.s 5))),
  -- [exact]
  fun f => (f.s' 5 - ((f.s 0 * f.s 2) + ((1 - f.s 0) * f.s 6))),
  -- [exact]
  fun f => (f.s' 6 - ((f.s 0 * f.s 3) + ((1 - f.s 0) * f.s 7))),
  -- [exact]
  fun f => (f.s' 7 - ((f.s 0 * f.s 4) + ((1 - f.s 0) * f.s 8)))
]

/-- DUP: 1 constraint(s). -/
def dup : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 0)
]

/-- DUP1: 1 constraint(s). -/
def dup1 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 1)
]

/-- DUP11: 1 constraint(s). -/
def dup11 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 11)
]

/-- DUP13: 1 constraint(s). -/
def dup13 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 13)
]

/-- DUP15: 1 constraint(s). -/
def dup15 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 15)
]

/-- DUP2: 1 constraint(s). -/
def dup2 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 2)
]

/-- DUP3: 1 constraint(s). -/
def dup3 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 3)
]

/-- DUP4: 1 constraint(s). -/
def dup4 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 4)
]

/-- DUP5: 1 constraint(s). -/
def dup5 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 5)
]

/-- DUP6: 1 constraint(s). -/
def dup6 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 6)
]

/-- DUP7: 1 constraint(s). -/
def dup7 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 7)
]

/-- DUP9: 1 constraint(s). -/
def dup9 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 9)
]

/-- MOVDN2: 1 constraint(s). -/
def movdn2 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 2 - f.s 0)
]

/-- MOVDN3: 1 constraint(s). -/
def movdn3 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 3 - f.s 0)
]

/-- MOVDN4: 1 constraint(s). -/
def movdn4 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 4 - f.s 0)
]

/-- MOVDN5: 1 constraint(s). -/
def movdn5 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 5 - f.s 0)
]

/-- MOVDN6: 1 constraint(s). -/
def movdn6 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 6 - f.s 0)
]

/-- MOVDN7: 1 constraint(s). -/
def movdn7 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 7 - f.s 0)
]

/-- MOVDN8: 1 constraint(s). -/
def movdn8 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 8 - f.s 0)
]

/-- MOVUP2: 1 constraint(s). -/
def movup2 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 2)
]

/-- MOVUP3: 1 constraint(s). -/
def movup3 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 3)
]

/-- MOVUP4: 1 constraint(s). -/
def movup4 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 4)
]

/-- MOVUP5: 1 constraint(s). -/
def movup5 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 5)
]

/-- MOVUP6: 1 constraint(s). -/
def movup6 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 6)
]

/-- MOVUP7: 1 constraint(s). -/
def movup7 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 7)
]

/-- MOVUP8: 1 constraint(s). -/
def movup8 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 8)
]

/-- PAD: 1 constraint(s). -/
def pad : ConstraintSet := [
  -- [exact]
  fun f => f.s' 0
]

/-- SDEPTH: 1 constraint(s). -/
def sdepth : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.b0)
]

/-- SWAP: 2 constraint(s). -/
def swap : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 1),
  -- [exact]
  fun f => (f.s' 1 - f.s 0)
]

/-- SWAPDW: 16 constraint(s). -/
def swapdw : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 8),
  -- [exact]
  fun f => (f.s' 1 - f.s 9),
  -- [exact]
  fun f => (f.s' 2 - f.s 10),
  -- [exact]
  fun f => (f.s' 3 - f.s 11),
  -- [exact]
  fun f => (f.s' 4 - f.s 12),
  -- [exact]
  fun f => (f.s' 5 - f.s 13),
  -- [exact]
  fun f => (f.s' 6 - f.s 14),
  -- [exact]
  fun f => (f.s' 7 - f.s 15),
  -- [exact]
  fun f => (f.s' 8 - f.s 0),
  -- [exact]
  fun f => (f.s' 9 - f.s 1),
  -- [exact]
  fun f => (f.s' 10 - f.s 2),
  -- [exact]
  fun f => (f.s' 11 - f.s 3),
  -- [exact]
  fun f => (f.s' 12 - f.s 4),
  -- [exact]
  fun f => (f.s' 13 - f.s 5),
  -- [exact]
  fun f => (f.s' 14 - f.s 6),
  -- [exact]
  fun f => (f.s' 15 - f.s 7)
]

/-- SWAPW: 8 constraint(s). -/
def swapw : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 4),
  -- [exact]
  fun f => (f.s' 1 - f.s 5),
  -- [exact]
  fun f => (f.s' 2 - f.s 6),
  -- [exact]
  fun f => (f.s' 3 - f.s 7),
  -- [exact]
  fun f => (f.s' 4 - f.s 0),
  -- [exact]
  fun f => (f.s' 5 - f.s 1),
  -- [exact]
  fun f => (f.s' 6 - f.s 2),
  -- [exact]
  fun f => (f.s' 7 - f.s 3)
]

/-- SWAPW2: 8 constraint(s). -/
def swapw2 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 8),
  -- [exact]
  fun f => (f.s' 1 - f.s 9),
  -- [exact]
  fun f => (f.s' 2 - f.s 10),
  -- [exact]
  fun f => (f.s' 3 - f.s 11),
  -- [exact]
  fun f => (f.s' 8 - f.s 0),
  -- [exact]
  fun f => (f.s' 9 - f.s 1),
  -- [exact]
  fun f => (f.s' 10 - f.s 2),
  -- [exact]
  fun f => (f.s' 11 - f.s 3)
]

/-- SWAPW3: 8 constraint(s). -/
def swapw3 : ConstraintSet := [
  -- [exact]
  fun f => (f.s' 0 - f.s 12),
  -- [exact]
  fun f => (f.s' 1 - f.s 13),
  -- [exact]
  fun f => (f.s' 2 - f.s 14),
  -- [exact]
  fun f => (f.s' 3 - f.s 15),
  -- [exact]
  fun f => (f.s' 12 - f.s 0),
  -- [exact]
  fun f => (f.s' 13 - f.s 1),
  -- [exact]
  fun f => (f.s' 14 - f.s 2),
  -- [exact]
  fun f => (f.s' 15 - f.s 3)
]

end MidenLean.AIR.Constraints
