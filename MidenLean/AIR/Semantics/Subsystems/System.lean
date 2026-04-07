import MidenLean.AIR.Semantics.Check
/-!
# System AIR Implementation Layer

This file encodes the canonical system-component AIR slice backed by
`air/src/constraints/system/mod.rs`: clock, execution context, and function-hash
transitions.

Each transition rule follows the Rust-backed gated pattern

`is_transition * selector * body = 0`.

The first-row clock rule is a genuine boundary constraint, so it uses the
explicit first-row selector rather than `whenTransition`.
-/

namespace MidenLean.AIR.Semantics.Subsystems.System

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder
open MidenLean.AIR.Semantics.Check

/-- Current-row clock column (`col 0`). -/
def clkCol : MainCol := ⟨0, by decide⟩
/-- Current-row context column (`col 1`). -/
def ctxCol : MainCol := ⟨1, by decide⟩
/-- Current-row `fn_hash[0]` column (`col 2`). -/
def fnHash0Col : MainCol := ⟨2, by decide⟩
/-- Current-row `fn_hash[1]` column (`col 3`). -/
def fnHash1Col : MainCol := ⟨3, by decide⟩
/-- Current-row `fn_hash[2]` column (`col 4`). -/
def fnHash2Col : MainCol := ⟨4, by decide⟩
/-- Current-row `fn_hash[3]` column (`col 5`). -/
def fnHash3Col : MainCol := ⟨5, by decide⟩

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

/-- Current-row decoder hasher-state `h0` column (`col 14`). -/
def decoderH0Col : MainCol := ⟨14, by decide⟩
/-- Current-row decoder hasher-state `h1` column (`col 15`). -/
def decoderH1Col : MainCol := ⟨15, by decide⟩
/-- Current-row decoder hasher-state `h2` column (`col 16`). -/
def decoderH2Col : MainCol := ⟨16, by decide⟩
/-- Current-row decoder hasher-state `h3` column (`col 17`). -/
def decoderH3Col : MainCol := ⟨17, by decide⟩

/-- Current-row clock expression `clk`. -/
def clk : FExpr := FExpr.curr clkCol
/-- Next-row clock expression `clk'`. -/
def clkNext : FExpr := FExpr.next clkCol
/-- Current-row context expression `ctx`. -/
def ctx : FExpr := FExpr.curr ctxCol
/-- Next-row context expression `ctx'`. -/
def ctxNext : FExpr := FExpr.next ctxCol
/-- Current-row `fn_hash[0]` expression. -/
def fnHash0 : FExpr := FExpr.curr fnHash0Col
/-- Current-row `fn_hash[1]` expression. -/
def fnHash1 : FExpr := FExpr.curr fnHash1Col
/-- Current-row `fn_hash[2]` expression. -/
def fnHash2 : FExpr := FExpr.curr fnHash2Col
/-- Current-row `fn_hash[3]` expression. -/
def fnHash3 : FExpr := FExpr.curr fnHash3Col
/-- Next-row `fn_hash[0]` expression. -/
def fnHash0Next : FExpr := FExpr.next fnHash0Col
/-- Next-row `fn_hash[1]` expression. -/
def fnHash1Next : FExpr := FExpr.next fnHash1Col
/-- Next-row `fn_hash[2]` expression. -/
def fnHash2Next : FExpr := FExpr.next fnHash2Col
/-- Next-row `fn_hash[3]` expression. -/
def fnHash3Next : FExpr := FExpr.next fnHash3Col

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

/-- Current-row decoder hasher-state `h0` expression. -/
def decoderH0 : FExpr := FExpr.curr decoderH0Col
/-- Current-row decoder hasher-state `h1` expression. -/
def decoderH1 : FExpr := FExpr.curr decoderH1Col
/-- Current-row decoder hasher-state `h2` expression. -/
def decoderH2 : FExpr := FExpr.curr decoderH2Col
/-- Current-row decoder hasher-state `h3` expression. -/
def decoderH3 : FExpr := FExpr.curr decoderH3Col

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

/-- Shared flag for `CALL`/`DYNCALL` context creation and fn-hash loading. -/
def callDyncallFlag : FExpr := FExpr.plus isCall isDyncall

/-- Shared flag for operations which change execution context. -/
def changeCtxFlag : FExpr :=
  FExpr.plus isCall (FExpr.plus isSyscall (FExpr.plus isDyncall isEnd))

/-- Default context-preservation flag `1 - isCall - isSyscall - isDyncall - isEnd`. -/
def defaultCtxFlag : FExpr := FExpr.minus (FExpr.const 1) changeCtxFlag

/-- Shared fn-hash load flag `isCall + isDyncall`. -/
def loadFlag : FExpr := callDyncallFlag

/-- Shared fn-hash preserve flag `1 - loadFlag - isEnd`. -/
def preserveFlag : FExpr := FExpr.minus (FExpr.const 1) (FExpr.plus loadFlag isEnd)

/-- Canonical AIR boundary constraint `clk[0] = 0`. -/
def clkFirst : BaseConstraint :=
  gate (FExpr.boundary BoundaryFlag.first) <| assertEq clk (FExpr.const 0)

/-- Canonical AIR transition constraint `clk' = clk + 1`. -/
def clkTransition : BaseConstraint :=
  whenTransition <| assertEq clkNext (FExpr.plus clk (FExpr.const 1))

/-- Canonical AIR context constraint for `CALL`/`DYNCALL`. -/
def ctxCallDyncall : BaseConstraint :=
  whenTransition <| gate callDyncallFlag <| assertEq ctxNext (FExpr.plus clk (FExpr.const 1))

/-- Canonical AIR context constraint for `SYSCALL`. -/
def ctxSyscall : BaseConstraint :=
  whenTransition <| gate isSyscall <| assertEq ctxNext (FExpr.const 0)

/-- Canonical AIR default context-preservation constraint. -/
def ctxDefault : BaseConstraint :=
  whenTransition <| gate defaultCtxFlag <| assertEq ctxNext ctx

/-- Canonical AIR fn-hash load constraint for `fn_hash[0]`. -/
def fnHash0Load : BaseConstraint :=
  whenTransition <| gate loadFlag <| assertEq fnHash0Next decoderH0

/-- Canonical AIR fn-hash load constraint for `fn_hash[1]`. -/
def fnHash1Load : BaseConstraint :=
  whenTransition <| gate loadFlag <| assertEq fnHash1Next decoderH1

/-- Canonical AIR fn-hash load constraint for `fn_hash[2]`. -/
def fnHash2Load : BaseConstraint :=
  whenTransition <| gate loadFlag <| assertEq fnHash2Next decoderH2

/-- Canonical AIR fn-hash load constraint for `fn_hash[3]`. -/
def fnHash3Load : BaseConstraint :=
  whenTransition <| gate loadFlag <| assertEq fnHash3Next decoderH3

/-- Canonical AIR fn-hash preservation constraint for `fn_hash[0]`. -/
def fnHash0Preserve : BaseConstraint :=
  whenTransition <| gate preserveFlag <| assertEq fnHash0Next fnHash0

/-- Canonical AIR fn-hash preservation constraint for `fn_hash[1]`. -/
def fnHash1Preserve : BaseConstraint :=
  whenTransition <| gate preserveFlag <| assertEq fnHash1Next fnHash1

/-- Canonical AIR fn-hash preservation constraint for `fn_hash[2]`. -/
def fnHash2Preserve : BaseConstraint :=
  whenTransition <| gate preserveFlag <| assertEq fnHash2Next fnHash2

/-- Canonical AIR fn-hash preservation constraint for `fn_hash[3]`. -/
def fnHash3Preserve : BaseConstraint :=
  whenTransition <| gate preserveFlag <| assertEq fnHash3Next fnHash3

/-- Canonical system-component base constraints. -/
def base : BaseConstraintSet := allOf
  [clkFirst, clkTransition,
   ctxCallDyncall, ctxSyscall, ctxDefault,
   fnHash0Load, fnHash1Load, fnHash2Load, fnHash3Load,
   fnHash0Preserve, fnHash1Preserve, fnHash2Preserve, fnHash3Preserve]

private def clockCurr (j : MainCol) : Felt :=
  match j.val with
  | 0 => 5
  | _ => 0

private def goodClockNext (j : MainCol) : Felt :=
  match j.val with
  | 0 => 6
  | _ => 0

private def badClockNext (j : MainCol) : Felt :=
  match j.val with
  | 0 => 7
  | _ => 0

private def goodClockRow : AirRow := {
  curr := clockCurr
  next := goodClockNext
  isTransition := 1
}

private def badClockRow : AirRow := {
  curr := clockCurr
  next := badClockNext
  isTransition := 1
}

#eval checkBase goodClockRow base
#eval checkBase badClockRow base

end MidenLean.AIR.Semantics.Subsystems.System
