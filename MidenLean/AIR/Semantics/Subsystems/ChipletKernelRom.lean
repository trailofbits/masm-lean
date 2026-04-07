import MidenLean.AIR.Semantics.Subsystems.ChipletSelectors
/-!
# Kernel ROM Chiplet AIR Implementation Layer

This file encodes the canonical kernel-ROM-chiplet main-trace AIR slice backed
by `air/src/constraints/chiplets/kernel_rom.rs`.

The shared chiplet trace begins at `CHIPLETS_OFFSET = 51`. Under the canonical
five-selector layout, the top-level chiplet selectors occupy `cols 51..55` and
the kernel ROM payload begins at `col 56`. Kernel ROM is active when
`s0 = 1`, `s1 = 1`, `s2 = 1`, `s3 = 1`, and `s4 = 0`. The resulting layout is:

- shared selectors: `s0 = col 51`, `s1 = col 52`, `s2 = col 53`,
  `s3 = col 54`, `s4 = col 55`
- `sfirst = col 56`
- `r0 = col 57`
- `r1 = col 58`
- `r2 = col 59`
- `r3 = col 60`

Rust enforces exactly 6 base constraints in this order:

1. `sfirst` is binary on kernel ROM rows.
2. When the next row remains in kernel ROM and does not start a new digest
   block, `r0'..r3'` stay equal to `r0..r3`.
3. The first kernel-ROM row entered from ACE has `sfirst' = 1`.
-/

namespace MidenLean.AIR.Semantics.Subsystems.ChipletKernelRom

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder
open MidenLean.AIR.Semantics.Check

/-- Shared chiplet trace offset `CHIPLETS_OFFSET = 51`. -/
abbrev chipletsOffset : Nat :=
  MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.chipletsOffset

/-- First kernel ROM payload column under the shared five-selector layout
(`col 56`). -/
abbrev kernelRomTraceOffset : Nat := chipletsOffset + 5

/-- Typed digest lane index `0..3`. -/
abbrev DigestIndex := Fin 4

/-- Next-row shared selector `s3'`. -/
abbrev s3Next : FExpr := MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.s3Next

/-- Next-row shared selector `s4'`. -/
abbrev s4Next : FExpr := MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.s4Next

/-- Current-row `sfirst` column (`col 56`). -/
def sfirstCol : MainCol := ⟨kernelRomTraceOffset, by decide⟩

/-- Current-row digest lane `r[i]` (`cols 57..60`). -/
def digestCol (i : DigestIndex) : MainCol := ⟨kernelRomTraceOffset + 1 + i.val, by
  have hlt : kernelRomTraceOffset + 1 + i.val < kernelRomTraceOffset + 1 + 4 :=
    Nat.add_lt_add_left i.is_lt (kernelRomTraceOffset + 1)
  exact lt_of_lt_of_le hlt (by decide)
⟩

/-- Current-row kernel-ROM-active flag `s0 * s1 * s2 * s3 * (1 - s4)`. -/
abbrev kernelRomFlag : FExpr :=
  MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.kernelRomChipletFlag

/-- Current-row ACE-active flag `s0 * s1 * s2 * (1 - s3)`. -/
abbrev aceFlag : FExpr :=
  MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.aceChipletFlag

/-- Current-row `sfirst`. -/
def sfirst : FExpr := FExpr.curr sfirstCol

/-- Next-row `sfirst'`. -/
def sfirstNext : FExpr := FExpr.next sfirstCol

/-- Current-row digest lane `r[i]`. -/
def digest (i : DigestIndex) : FExpr := FExpr.curr (digestCol i)

/-- Next-row digest lane `r'[i]`. -/
def digestNext (i : DigestIndex) : FExpr := FExpr.next (digestCol i)

/-- Constant `1`. -/
def one : FExpr := FExpr.const 1

/-- Canonical complement expression `1 - expr`. -/
def oneMinus (expr : FExpr) : FExpr := FExpr.minus one expr

/-- Canonical integrity-gated zero constraint. -/
def integrityZero (selector expr : FExpr) : BaseConstraint :=
  gate selector <| assertZero expr

/-- Canonical transition-gated equality constraint. -/
def transitionEq (selector lhs rhs : FExpr) : BaseConstraint :=
  whenTransition <| gate selector <| assertEq lhs rhs

/-- Next-row kernel-ROM activity selector `s3' * (1 - s4')`. -/
def kernelRomNext : FExpr := FExpr.times s3Next (oneMinus s4Next)

/-- Shared digest-contiguity gate
`kernel_rom_flag * (1 - s4') * (1 - sfirst')`. -/
def contiguityGate : FExpr :=
  FExpr.times (FExpr.times kernelRomFlag (oneMinus s4Next)) (oneMinus sfirstNext)

/-- Selector for the first kernel-ROM row entered from ACE. -/
def flagNextRowFirstKernelRom : FExpr := FExpr.times aceFlag kernelRomNext

/-- Canonical AIR binary constraint for `sfirst`. -/
def sfirstBinary : BaseConstraint :=
  integrityZero kernelRomFlag <| FExpr.times sfirst (FExpr.minus sfirst one)

/-- Canonical AIR digest-contiguity constraint for lane `i`. -/
def digestContiguity (i : DigestIndex) : BaseConstraint :=
  transitionEq contiguityGate (digestNext i) (digest i)

/-- Canonical AIR first-row constraint `sfirst' = 1` when entering kernel ROM
from ACE. -/
def firstRowStart : BaseConstraint :=
  transitionEq flagNextRowFirstKernelRom sfirstNext one

/-- Canonical digest-contiguity constraints in Rust assertion order. -/
def digestContiguityConstraints : BaseConstraintSet :=
  List.ofFn fun i : DigestIndex => digestContiguity i

/-- Canonical kernel-ROM base constraints in Rust assertion order. -/
def base : BaseConstraintSet := allOf <|
  [sfirstBinary] ++ digestContiguityConstraints ++ [firstRowStart]

private def kernelRomCols
    (s0Val s1Val s2Val s3Val s4Val sfirstVal r0Val r1Val r2Val r3Val : Felt)
    (j : MainCol) : Felt :=
  match j.val with
  | 51 => s0Val
  | 52 => s1Val
  | 53 => s2Val
  | 54 => s3Val
  | 55 => s4Val
  | 56 => sfirstVal
  | 57 => r0Val
  | 58 => r1Val
  | 59 => r2Val
  | 60 => r3Val
  | _ => 0

private def aceStub : MainCol → Felt :=
  kernelRomCols 1 1 1 0 0 0 0 0 0 0

private def goodEntryRow : AirRow := {
  curr := aceStub
  next := kernelRomCols 1 1 1 1 0 1 9 8 7 6
  isTransition := 1
}

private def badEntryRow : AirRow := {
  curr := aceStub
  next := kernelRomCols 1 1 1 1 0 0 9 8 7 6
  isTransition := 1
}

private def goodContiguousRow : AirRow := {
  curr := kernelRomCols 1 1 1 1 0 1 9 8 7 6
  next := kernelRomCols 1 1 1 1 0 0 9 8 7 6
  isTransition := 1
}

private def badContiguousRow : AirRow := {
  curr := kernelRomCols 1 1 1 1 0 1 9 8 7 6
  next := kernelRomCols 1 1 1 1 0 0 9 8 99 6
  isTransition := 1
}

private def goodNewBlockRow : AirRow := {
  curr := kernelRomCols 1 1 1 1 0 1 9 8 7 6
  next := kernelRomCols 1 1 1 1 0 1 1 2 3 4
  isTransition := 1
}

private def badBinaryRow : AirRow := {
  curr := kernelRomCols 1 1 1 1 0 2 9 8 7 6
  next := kernelRomCols 1 1 1 1 0 0 9 8 7 6
  isTransition := 1
}

#eval checkBase goodEntryRow base
#eval checkBase badEntryRow base
#eval checkBase goodContiguousRow base
#eval checkBase badContiguousRow base
#eval checkBase goodNewBlockRow base
#eval checkBase badBinaryRow base

end MidenLean.AIR.Semantics.Subsystems.ChipletKernelRom
