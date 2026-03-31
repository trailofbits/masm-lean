import MidenLean.AIR.Semantics.Subsystems.StackArith
/-!
# Intended StackArith Spec (bounded `u32` slice)

This file keeps the intended mathematical spec for the currently known
`StackArith` divergence instead of weakening the spec to match the current
Rust AIR.

For `U32ADD` and `U32ADD3`, the design docs specify that the high visible
output is the carry (`h2`) and that `h3 = 0`. The current Rust AIR instead
uses the more permissive shared relation `s1' = h3 * 2^16 + h2`.

For `U32SUB`, the design docs also specify that the unused high helper limbs
`h2` and `h3` are zero. The current Rust AIR enforces the visible subtraction
relations, but does not constrain those helper limbs.

The implementation layer in `Subsystems.StackArith` intentionally continues to
mirror Rust exactly. This file stores the stronger intended constraints.
-/

namespace MidenLean.AIR.Semantics.Spec.StackArith

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder

/-- Intended `U32ADD` low-output relation from the design docs:
`s0' = 2^16 * h1 + h0`. -/
def u32AddLo : BaseConstraint :=
  whenTransition <|
    gate MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Add <|
      assertEq MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next
        MidenLean.AIR.Semantics.Subsystems.StackArith.u32VLo

/-- Intended `U32ADD` high-output/carry relation from the design docs:
`s1' = h2`. -/
def u32AddCarry : BaseConstraint :=
  whenTransition <|
    gate MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Add <|
      assertEq MidenLean.AIR.Semantics.Subsystems.StackArith.s1Next
        MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2

/-- Intended `U32ADD` helper-limb relation from the design docs:
`h3 = 0`. -/
def u32AddH3Zero : BaseConstraint :=
  gate MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Add <|
    assertEq MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3 (FExpr.const 0)

/-- Intended `U32ADD` bounded spec. -/
def u32Add : BaseConstraintSet := allOf
  [u32AddLo, u32AddCarry, u32AddH3Zero,
   MidenLean.AIR.Semantics.Subsystems.StackArith.u32AddInput]

/-- Intended `U32ADD3` low-output relation from the design docs:
`s0' = 2^16 * h1 + h0`. -/
def u32Add3Lo : BaseConstraint :=
  whenTransition <|
    gate MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Add3 <|
      assertEq MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next
        MidenLean.AIR.Semantics.Subsystems.StackArith.u32VLo

/-- Intended `U32ADD3` high-output/carry relation from the design docs:
`s1' = h2`. -/
def u32Add3Carry : BaseConstraint :=
  whenTransition <|
    gate MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Add3 <|
      assertEq MidenLean.AIR.Semantics.Subsystems.StackArith.s1Next
        MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2

/-- Intended `U32ADD3` helper-limb relation from the design docs:
`h3 = 0`. -/
def u32Add3H3Zero : BaseConstraint :=
  gate MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Add3 <|
    assertEq MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3 (FExpr.const 0)

/-- Intended `U32ADD3` bounded spec. -/
def u32Add3 : BaseConstraintSet := allOf
  [u32Add3Lo, u32Add3Carry, u32Add3H3Zero,
   MidenLean.AIR.Semantics.Subsystems.StackArith.u32Add3Input]

/-- Intended `U32SUB` difference relation from the design docs:
`s1 = s0 + s1' - 2^32 * s0'`. -/
def u32SubDiff : BaseConstraint :=
  whenTransition <|
    gate MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Sub <|
      assertEq MidenLean.AIR.Semantics.Subsystems.StackArith.s1
        (FExpr.minus
          (FExpr.plus MidenLean.AIR.Semantics.Subsystems.StackArith.s0
            MidenLean.AIR.Semantics.Subsystems.StackArith.s1Next)
          (FExpr.times MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next
            MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow32))

/-- Intended `U32SUB` borrow-binaryity relation from the design docs:
`s0'^2 - s0' = 0`. -/
def u32SubBorrowBinary : BaseConstraint :=
  whenTransition <|
    gate MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Sub <|
      assertZero
        (FExpr.times MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next
          (FExpr.minus MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next (FExpr.const 1)))

/-- Intended `U32SUB` low-output relation from the design docs:
`s1' = 2^16 * h1 + h0`. -/
def u32SubLow : BaseConstraint :=
  whenTransition <|
    gate MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Sub <|
      assertEq MidenLean.AIR.Semantics.Subsystems.StackArith.s1Next
        MidenLean.AIR.Semantics.Subsystems.StackArith.u32VLo

/-- Intended `U32SUB` helper-limb relation from the design docs:
`h2 = 0`. -/
def u32SubH2Zero : BaseConstraint :=
  gate MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Sub <|
    assertEq MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2 (FExpr.const 0)

/-- Intended `U32SUB` helper-limb relation from the design docs:
`h3 = 0`. -/
def u32SubH3Zero : BaseConstraint :=
  gate MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Sub <|
    assertEq MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3 (FExpr.const 0)

/-- Intended `U32SUB` bounded spec. -/
def u32Sub : BaseConstraintSet := allOf
  [u32SubDiff, u32SubBorrowBinary, u32SubLow, u32SubH2Zero, u32SubH3Zero]

end MidenLean.AIR.Semantics.Spec.StackArith
