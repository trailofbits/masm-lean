import MidenLean.AIR.Semantics.Check
/-!
# Stack Overflow AIR Implementation Layer

This file encodes the canonical stack-overflow bookkeeping slice backed by
`air/src/constraints/stack/overflow/mod.rs`.

The relevant main-trace layout is:

- `clk`: `col 0`
- visible stack `s0..s15`: `cols 30..45`
- stack depth `b0`: `col 46`
- overflow address `b1`: `col 47`
- overflow helper `h0`: `col 48`
- decoder op bits `b0..b6`: `cols 7..13`

The depth-transition polynomial mirrors the Rust masking structure for
`CALL`/`DYNCALL`/`SYSCALL` entry and `END`-of-call rows. The aggregate
`leftShift` and `rightShift` flags are temporary low-degree proxies derived
from op-bit prefixes until the exact `OpFlags` bridge is added.
-/

namespace MidenLean.AIR.Semantics.Subsystems.StackOverflow

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder
open MidenLean.AIR.Semantics.Check

/-- Current-row clock column (`col 0`). -/
def clkCol : MainCol := ⟨0, by decide⟩

/-- Current-row decoder flag `b0` (`col 7`). -/
def opBit0Col : MainCol := ⟨7, by decide⟩
/-- Current-row decoder flag `b1` (`col 8`). -/
def opBit1Col : MainCol := ⟨8, by decide⟩
/-- Current-row decoder flag `b2` (`col 9`). -/
def opBit2Col : MainCol := ⟨9, by decide⟩
/-- Current-row decoder flag `b3` (`col 10`). -/
def opBit3Col : MainCol := ⟨10, by decide⟩
/-- Current-row decoder flag `b4` (`col 11`). -/
def opBit4Col : MainCol := ⟨11, by decide⟩
/-- Current-row decoder flag `b5` (`col 12`). -/
def opBit5Col : MainCol := ⟨12, by decide⟩
/-- Current-row decoder flag `b6` (`col 13`). -/
def opBit6Col : MainCol := ⟨13, by decide⟩

/-- Decoder flag indicating `END` of a `CALL`/`DYNCALL` block (`col 20`). -/
def isCallEndCol : MainCol := ⟨20, by decide⟩
/-- Decoder flag indicating `END` of a `SYSCALL` block (`col 21`). -/
def isSyscallEndCol : MainCol := ⟨21, by decide⟩

/-- Visible-stack `s15` column (`col 45`). -/
def s15Col : MainCol := ⟨45, by decide⟩
/-- Stack depth bookkeeping column `b0` (`col 46`). -/
def stackDepthCol : MainCol := ⟨46, by decide⟩
/-- Overflow address bookkeeping column `b1` (`col 47`). -/
def overflowAddrCol : MainCol := ⟨47, by decide⟩
/-- Overflow helper register `h0` (`col 48`). -/
def overflowHelperCol : MainCol := ⟨48, by decide⟩

/-- Current-row clock expression `clk`. -/
def clk : FExpr := FExpr.curr clkCol

/-- Current-row decoder flag expression `b0`. -/
def opBit0 : FExpr := FExpr.curr opBit0Col
/-- Current-row decoder flag expression `b1`. -/
def opBit1 : FExpr := FExpr.curr opBit1Col
/-- Current-row decoder flag expression `b2`. -/
def opBit2 : FExpr := FExpr.curr opBit2Col
/-- Current-row decoder flag expression `b3`. -/
def opBit3 : FExpr := FExpr.curr opBit3Col
/-- Current-row decoder flag expression `b4`. -/
def opBit4 : FExpr := FExpr.curr opBit4Col
/-- Current-row decoder flag expression `b5`. -/
def opBit5 : FExpr := FExpr.curr opBit5Col
/-- Current-row decoder flag expression `b6`. -/
def opBit6 : FExpr := FExpr.curr opBit6Col

def notOpBit0 : FExpr := FExpr.minus (FExpr.const 1) opBit0
def notOpBit1 : FExpr := FExpr.minus (FExpr.const 1) opBit1
def notOpBit2 : FExpr := FExpr.minus (FExpr.const 1) opBit2
def notOpBit3 : FExpr := FExpr.minus (FExpr.const 1) opBit3
def notOpBit4 : FExpr := FExpr.minus (FExpr.const 1) opBit4
def notOpBit5 : FExpr := FExpr.minus (FExpr.const 1) opBit5
def notOpBit6 : FExpr := FExpr.minus (FExpr.const 1) opBit6

/-- Current-row `END`-of-call flag. -/
def isCallEndFlag : FExpr := FExpr.curr isCallEndCol
/-- Current-row `END`-of-syscall flag. -/
def isSyscallEndFlag : FExpr := FExpr.curr isSyscallEndCol

/-- Current-row visible-stack tail `s15`. -/
def s15 : FExpr := FExpr.curr s15Col
/-- Next-row visible-stack tail `s15'`. -/
def s15Next : FExpr := FExpr.next s15Col
/-- Current-row stack depth `b0`. -/
def stackDepth : FExpr := FExpr.curr stackDepthCol
/-- Next-row stack depth `b0'`. -/
def stackDepthNext : FExpr := FExpr.next stackDepthCol
/-- Current-row overflow address `b1`. -/
def overflowAddr : FExpr := FExpr.curr overflowAddrCol
/-- Next-row overflow address `b1'`. -/
def overflowAddrNext : FExpr := FExpr.next overflowAddrCol
/-- Current-row overflow helper `h0`. -/
def overflowHelper : FExpr := FExpr.curr overflowHelperCol

/-- Degree-3 prefix `010` used as a temporary low-degree proxy for aggregate
left-shift behavior. -/
def prefix010 : FExpr :=
  FExpr.times notOpBit6 (FExpr.times opBit5 notOpBit4)

/-- Degree-3 prefix `011` used as a temporary low-degree proxy for aggregate
right-shift behavior. -/
def prefix011 : FExpr :=
  FExpr.times notOpBit6 (FExpr.times opBit5 opBit4)

/-- Approximate aggregate `right_shift` flag.

TODO: replace this with the exact bridge from Rust
`constraints/op_flags/mod.rs`, namely `prefix_011 + PUSH + U32SPLIT`. -/
def rightShift : FExpr := prefix011

/-- Approximate aggregate `left_shift` flag.

TODO: replace this with the exact bridge from Rust
`constraints/op_flags/mod.rs`, namely
`prefix_010 + add3_madd_prefix + split_loop_flag + REPEAT + shift_left_on_end + DYN`.
The exact Rust aggregate intentionally excludes `DYNCALL`. -/
def leftShift : FExpr := prefix010

/-- Exact overflow flag `(b0 - 16) * h0`. -/
def overflow : FExpr :=
  FExpr.times (FExpr.minus stackDepth (FExpr.const 16)) overflowHelper

/-- Canonical selector for the `CALL` opcode `110_1100` (`b6..b0`). -/
def isCall : FExpr :=
  FExpr.times opBit6
    (FExpr.times opBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for the `SYSCALL` opcode `110_1000` (`b6..b0`). -/
def isSyscall : FExpr :=
  FExpr.times opBit6
    (FExpr.times opBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for the `DYNCALL` opcode `101_1100` (`b6..b0`). -/
def isDyncall : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for the `END` opcode `111_0000` (`b6..b0`). -/
def isEnd : FExpr :=
  FExpr.times opBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Shared entry flag `CALL + DYNCALL + SYSCALL` for depth-reset rows. -/
def callOrDyncallOrSyscall : FExpr :=
  FExpr.plus isCall (FExpr.plus isDyncall isSyscall)

/-- Shared `END`-of-call flag used to suppress the generic shift law on return
rows. -/
def callOrDyncallOrSyscallEnd : FExpr :=
  FExpr.times isEnd (FExpr.plus isCallEndFlag isSyscallEndFlag)

/-- Normal-row mask `1 - entryFlag - endFlag`. -/
def normalMask : FExpr :=
  FExpr.minus
    (FExpr.minus (FExpr.const 1) callOrDyncallOrSyscall)
    callOrDyncallOrSyscallEnd

/-- Boundary constraint `b0[first] = 16`. -/
def stackDepthFirst : BaseConstraint :=
  gate (FExpr.boundary BoundaryFlag.first) <| assertEq stackDepth (FExpr.const 16)

/-- Boundary constraint `b0[last] = 16`. -/
def stackDepthLast : BaseConstraint :=
  gate (FExpr.boundary BoundaryFlag.last) <| assertEq stackDepth (FExpr.const 16)

/-- Boundary constraint `b1[first] = 0`. -/
def overflowAddrFirst : BaseConstraint :=
  gate (FExpr.boundary BoundaryFlag.first) <| assertEq overflowAddr (FExpr.const 0)

/-- Boundary constraint `b1[last] = 0`. -/
def overflowAddrLast : BaseConstraint :=
  gate (FExpr.boundary BoundaryFlag.last) <| assertEq overflowAddr (FExpr.const 0)

/-- Stack-depth transition constraint mirroring Rust:

`(b0' - b0) * normalMask + leftShift * overflow - rightShift + callPart = 0`.

The `normalMask` and `callPart` keep the same shape as the Rust AIR; only the
aggregate shift flags are temporary approximations. -/
def stackDepthTransition : BaseConstraint :=
  let depthDeltaPart := FExpr.times (FExpr.minus stackDepthNext stackDepth) normalMask
  let leftShiftPart := FExpr.times leftShift overflow
  let rightShiftPart := rightShift
  let callPart := FExpr.times callOrDyncallOrSyscall (FExpr.minus stackDepthNext (FExpr.const 16))
  whenTransition <| assertZero <|
    FExpr.plus
      (FExpr.minus (FExpr.plus depthDeltaPart leftShiftPart) rightShiftPart)
      callPart

/-- Overflow-flag constraint `(1 - overflow) * (b0 - 16) = 0`. -/
def overflowFlag : BaseConstraint :=
  assertZero <|
    FExpr.times
      (FExpr.minus (FExpr.const 1) overflow)
      (FExpr.minus stackDepth (FExpr.const 16))

/-- Overflow-address transition constraint `rightShift * (b1' - clk) = 0`. -/
def overflowAddrTransition : BaseConstraint :=
  whenTransition <| assertZero <|
    FExpr.times rightShift (FExpr.minus overflowAddrNext clk)

/-- Zero-insert transition constraint
`(1 - overflow) * leftShift * s15' = 0`. -/
def zeroInsertTransition : BaseConstraint :=
  whenTransition <| assertZero <|
    FExpr.times
      (FExpr.minus (FExpr.const 1) overflow)
      (FExpr.times leftShift s15Next)

/-- Canonical stack-overflow bookkeeping constraints. -/
def base : BaseConstraintSet := allOf
  [stackDepthFirst,
   stackDepthLast,
   overflowAddrFirst,
   overflowAddrLast,
   stackDepthTransition,
   overflowFlag,
   overflowAddrTransition,
   zeroInsertTransition]

private def goodFirstBoundaryCurr (j : MainCol) : Felt :=
  match j.val with
  | 46 => 16
  | 47 => 0
  | _ => 0

private def badFirstBoundaryCurr (j : MainCol) : Felt :=
  match j.val with
  | 46 => 15
  | 47 => 1
  | _ => 0

private def goodFirstBoundaryRow : AirRow := {
  curr := goodFirstBoundaryCurr
  isFirst := 1
}

private def badFirstBoundaryRow : AirRow := {
  curr := badFirstBoundaryCurr
  isFirst := 1
}

#eval checkBase goodFirstBoundaryRow [stackDepthFirst, overflowAddrFirst]
#eval checkBase badFirstBoundaryRow [stackDepthFirst, overflowAddrFirst]

end MidenLean.AIR.Semantics.Subsystems.StackOverflow
