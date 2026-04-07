import MidenLean.AIR.Semantics.Check
/-!
# StackOps AIR Implementation Layer: Step 10 bounded slice

This file extends the Rust-facing `StackOps` implementation layer from `PAD`
only to the current bounded slice: `PAD`, the first `DUP` family slice
(`DUP0`-`DUP7`, `DUP9`, `DUP11`, `DUP13`, `DUP15`), `CLK`, `SWAP`, `ASSERT`,
`MOVUP2`-`MOVUP8`, `MOVDN2`-`MOVDN8`, `SWAPW`, `SWAPW2`, `SWAPW3`,
`SWAPDW`, `CSWAP`, `CSWAPW`, `CALLER`, and `SDEPTH`.

Each rule follows the documented and Rust-backed gated pattern

`is_transition * selector * body = 0`.

The integrity rules in this slice are `ASSERT`, `CSWAP`, and `CSWAPW`, so
those canonical forms are `selector * body = 0` without the transition
factor.

This subsystem file covers only op-specific stack-manipulation bodies. Shared
visible stack-shift behavior still belongs to `StackGeneral`.
-/

namespace MidenLean.AIR.Semantics.Subsystems.StackOps

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder
open MidenLean.AIR.Semantics.Check

/-- Current-row clock column (`col 0`). -/
def clkCol : MainCol := ⟨0, by decide⟩
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

/-- Visible-stack `s0` column (`col 30`). -/
def s0Col : MainCol := ⟨30, by decide⟩
/-- Visible-stack `s1` column (`col 31`). -/
def s1Col : MainCol := ⟨31, by decide⟩
/-- Visible-stack `s2` column (`col 32`). -/
def s2Col : MainCol := ⟨32, by decide⟩
/-- Visible-stack `s3` column (`col 33`). -/
def s3Col : MainCol := ⟨33, by decide⟩
/-- Visible-stack `s4` column (`col 34`). -/
def s4Col : MainCol := ⟨34, by decide⟩
/-- Visible-stack `s5` column (`col 35`). -/
def s5Col : MainCol := ⟨35, by decide⟩
/-- Visible-stack `s6` column (`col 36`). -/
def s6Col : MainCol := ⟨36, by decide⟩
/-- Visible-stack `s7` column (`col 37`). -/
def s7Col : MainCol := ⟨37, by decide⟩
/-- Visible-stack `s8` column (`col 38`). -/
def s8Col : MainCol := ⟨38, by decide⟩
/-- Visible-stack `s9` column (`col 39`). -/
def s9Col : MainCol := ⟨39, by decide⟩
/-- Visible-stack `s10` column (`col 40`). -/
def s10Col : MainCol := ⟨40, by decide⟩
/-- Visible-stack `s11` column (`col 41`). -/
def s11Col : MainCol := ⟨41, by decide⟩
/-- Visible-stack `s12` column (`col 42`). -/
def s12Col : MainCol := ⟨42, by decide⟩
/-- Visible-stack `s13` column (`col 43`). -/
def s13Col : MainCol := ⟨43, by decide⟩
/-- Visible-stack `s14` column (`col 44`). -/
def s14Col : MainCol := ⟨44, by decide⟩
/-- Visible-stack `s15` column (`col 45`). -/
def s15Col : MainCol := ⟨45, by decide⟩
/-- Visible stack-depth column (`col 46`). -/
def stackDepthCol : MainCol := ⟨46, by decide⟩

/-- Current-row clock expression `clk`. -/
def clkExpr : FExpr := FExpr.curr clkCol
/-- Current-row `fn_hash[0]` expression. -/
def fnHash0 : FExpr := FExpr.curr fnHash0Col
/-- Current-row `fn_hash[1]` expression. -/
def fnHash1 : FExpr := FExpr.curr fnHash1Col
/-- Current-row `fn_hash[2]` expression. -/
def fnHash2 : FExpr := FExpr.curr fnHash2Col
/-- Current-row `fn_hash[3]` expression. -/
def fnHash3 : FExpr := FExpr.curr fnHash3Col

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

/-- Canonical `s0` leaf used by the current stack-op AIR rules. -/
def s0 : FExpr := FExpr.curr s0Col
/-- Canonical `s1` leaf used by the current stack-op AIR rules. -/
def s1 : FExpr := FExpr.curr s1Col
/-- Canonical `s2` leaf used by the current stack-op AIR rules. -/
def s2 : FExpr := FExpr.curr s2Col
/-- Canonical `s3` leaf used by the current stack-op AIR rules. -/
def s3 : FExpr := FExpr.curr s3Col
/-- Canonical `s4` leaf used by the current stack-op AIR rules. -/
def s4 : FExpr := FExpr.curr s4Col
/-- Canonical `s5` leaf used by the current stack-op AIR rules. -/
def s5 : FExpr := FExpr.curr s5Col
/-- Canonical `s6` leaf used by the current stack-op AIR rules. -/
def s6 : FExpr := FExpr.curr s6Col
/-- Canonical `s7` leaf used by the current stack-op AIR rules. -/
def s7 : FExpr := FExpr.curr s7Col
/-- Canonical `s8` leaf used by the current stack-op AIR rules. -/
def s8 : FExpr := FExpr.curr s8Col
/-- Canonical `s9` leaf used by the current stack-op AIR rules. -/
def s9 : FExpr := FExpr.curr s9Col
/-- Canonical `s10` leaf used by the current stack-op AIR rules. -/
def s10 : FExpr := FExpr.curr s10Col
/-- Canonical `s11` leaf used by the current stack-op AIR rules. -/
def s11 : FExpr := FExpr.curr s11Col
/-- Canonical `s12` leaf used by the current stack-op AIR rules. -/
def s12 : FExpr := FExpr.curr s12Col
/-- Canonical `s13` leaf used by the current stack-op AIR rules. -/
def s13 : FExpr := FExpr.curr s13Col
/-- Canonical `s14` leaf used by the current stack-op AIR rules. -/
def s14 : FExpr := FExpr.curr s14Col
/-- Canonical `s15` leaf used by the current stack-op AIR rules. -/
def s15 : FExpr := FExpr.curr s15Col
/-- Canonical next-row `s0` leaf used by the current stack-op AIR rules. -/
def s0Next : FExpr := FExpr.next s0Col
/-- Canonical next-row `s1` leaf used by the current stack-op AIR rules. -/
def s1Next : FExpr := FExpr.next s1Col
/-- Canonical next-row `s2` leaf used by the current stack-op AIR rules. -/
def s2Next : FExpr := FExpr.next s2Col
/-- Canonical next-row `s3` leaf used by the current stack-op AIR rules. -/
def s3Next : FExpr := FExpr.next s3Col
/-- Canonical next-row `s4` leaf used by the current stack-op AIR rules. -/
def s4Next : FExpr := FExpr.next s4Col
/-- Canonical next-row `s5` leaf used by the current stack-op AIR rules. -/
def s5Next : FExpr := FExpr.next s5Col
/-- Canonical next-row `s6` leaf used by the current stack-op AIR rules. -/
def s6Next : FExpr := FExpr.next s6Col
/-- Canonical next-row `s7` leaf used by the current stack-op AIR rules. -/
def s7Next : FExpr := FExpr.next s7Col
/-- Canonical next-row `s8` leaf used by the current stack-op AIR rules. -/
def s8Next : FExpr := FExpr.next s8Col
/-- Canonical next-row `s9` leaf used by the current stack-op AIR rules. -/
def s9Next : FExpr := FExpr.next s9Col
/-- Canonical next-row `s10` leaf used by the current stack-op AIR rules. -/
def s10Next : FExpr := FExpr.next s10Col
/-- Canonical next-row `s11` leaf used by the current stack-op AIR rules. -/
def s11Next : FExpr := FExpr.next s11Col
/-- Canonical next-row `s12` leaf used by the current stack-op AIR rules. -/
def s12Next : FExpr := FExpr.next s12Col
/-- Canonical next-row `s13` leaf used by the current stack-op AIR rules. -/
def s13Next : FExpr := FExpr.next s13Col
/-- Canonical next-row `s14` leaf used by the current stack-op AIR rules. -/
def s14Next : FExpr := FExpr.next s14Col
/-- Canonical next-row `s15` leaf used by the current stack-op AIR rules. -/
def s15Next : FExpr := FExpr.next s15Col
/-- Canonical current-row stack-depth leaf for the visible stack segment. -/
def stackDepth : FExpr := FExpr.curr stackDepthCol

/-- Canonical selector for the `PAD` opcode `011_0000` (`b6..b0`). -/
def isPad : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical AIR constraint for `PAD`. -/
def pad : BaseConstraint :=
  whenTransition <| gate isPad <| assertZero s0Next

/-- Canonical selector for the `DUP0` opcode `011_0001` (`b6..b0`). -/
def isDup0 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 opBit0)))))

/-- Canonical selector for the `DUP1` opcode `011_0010` (`b6..b0`). -/
def isDup1 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 notOpBit0)))))

/-- Canonical selector for the `DUP2` opcode `011_0011` (`b6..b0`). -/
def isDup2 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 opBit0)))))

/-- Canonical selector for the `DUP3` opcode `011_0100` (`b6..b0`). -/
def isDup3 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for the `DUP4` opcode `011_0101` (`b6..b0`). -/
def isDup4 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 opBit0)))))

/-- Canonical selector for the `DUP5` opcode `011_0110` (`b6..b0`). -/
def isDup5 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times opBit1 notOpBit0)))))

/-- Canonical selector for the `DUP6` opcode `011_0111` (`b6..b0`). -/
def isDup6 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times opBit1 opBit0)))))

/-- Canonical selector for the `DUP7` opcode `011_1000` (`b6..b0`). -/
def isDup7 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for the `DUP9` opcode `011_1010` (`b6..b0`). -/
def isDup9 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 notOpBit0)))))

/-- Canonical selector for the `DUP11` opcode `011_1100` (`b6..b0`). -/
def isDup11 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for the `DUP13` opcode `011_1110` (`b6..b0`). -/
def isDup13 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times opBit2
            (FExpr.times opBit1 notOpBit0)))))

/-- Canonical selector for the `DUP15` opcode `011_1001` (`b6..b0`). -/
def isDup15 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 opBit0)))))

/-- Canonical AIR constraint for `DUP0`. -/
def dup0 : BaseConstraint :=
  whenTransition <| gate isDup0 <| assertEq s0Next s0

/-- Canonical AIR constraint for `DUP1`. -/
def dup1 : BaseConstraint :=
  whenTransition <| gate isDup1 <| assertEq s0Next s1

/-- Canonical AIR constraint for `DUP2`. -/
def dup2 : BaseConstraint :=
  whenTransition <| gate isDup2 <| assertEq s0Next s2

/-- Canonical AIR constraint for `DUP3`. -/
def dup3 : BaseConstraint :=
  whenTransition <| gate isDup3 <| assertEq s0Next s3

/-- Canonical AIR constraint for `DUP4`. -/
def dup4 : BaseConstraint :=
  whenTransition <| gate isDup4 <| assertEq s0Next s4

/-- Canonical AIR constraint for `DUP5`. -/
def dup5 : BaseConstraint :=
  whenTransition <| gate isDup5 <| assertEq s0Next s5

/-- Canonical AIR constraint for `DUP6`. -/
def dup6 : BaseConstraint :=
  whenTransition <| gate isDup6 <| assertEq s0Next s6

/-- Canonical AIR constraint for `DUP7`. -/
def dup7 : BaseConstraint :=
  whenTransition <| gate isDup7 <| assertEq s0Next s7

/-- Canonical AIR constraint for `DUP9`. -/
def dup9 : BaseConstraint :=
  whenTransition <| gate isDup9 <| assertEq s0Next s9

/-- Canonical AIR constraint for `DUP11`. -/
def dup11 : BaseConstraint :=
  whenTransition <| gate isDup11 <| assertEq s0Next s11

/-- Canonical AIR constraint for `DUP13`. -/
def dup13 : BaseConstraint :=
  whenTransition <| gate isDup13 <| assertEq s0Next s13

/-- Canonical AIR constraint for `DUP15`. -/
def dup15 : BaseConstraint :=
  whenTransition <| gate isDup15 <| assertEq s0Next s15

/-- Canonical selector for the `CLK` opcode `011_1011` (`b6..b0`). -/
def isClk : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 opBit0)))))

/-- Canonical selector for the `SWAP` opcode `000_1000` (`b6..b0`). -/
def isSwap : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for the `ASSERT` opcode `010_0000` (`b6..b0`). -/
def isAssert : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times notOpBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical AIR constraint for `CLK`. -/
def clk : BaseConstraint :=
  whenTransition <| gate isClk <| assertEq s0Next clkExpr

/-- Canonical AIR constraint for `SWAP` on `s0'`. -/
def swap0 : BaseConstraint :=
  whenTransition <| gate isSwap <| assertEq s0Next s1

/-- Canonical AIR constraint for `SWAP` on `s1'`. -/
def swap1 : BaseConstraint :=
  whenTransition <| gate isSwap <| assertEq s1Next s0

/-- Canonical AIR integrity constraint for `ASSERT`. -/
def assertOne : BaseConstraint :=
  gate isAssert <| assertEq s0 (FExpr.const 1)

/-- Canonical selector for the `MOVUP2` opcode `000_1010` (`b6..b0`). -/
def isMovup2 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 notOpBit0)))))

/-- Canonical selector for the `MOVUP3` opcode `000_1100` (`b6..b0`). -/
def isMovup3 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for the `MOVUP4` opcode `001_0000` (`b6..b0`). -/
def isMovup4 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for the `MOVUP5` opcode `001_0010` (`b6..b0`). -/
def isMovup5 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 notOpBit0)))))

/-- Canonical selector for the `MOVUP6` opcode `001_0100` (`b6..b0`). -/
def isMovup6 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for the `MOVUP7` opcode `001_0110` (`b6..b0`). -/
def isMovup7 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times opBit1 notOpBit0)))))

/-- Canonical selector for the `MOVUP8` opcode `001_1010` (`b6..b0`). -/
def isMovup8 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 notOpBit0)))))

/-- Canonical selector for the `MOVDN2` opcode `000_1011` (`b6..b0`). -/
def isMovdn2 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 opBit0)))))

/-- Canonical selector for the `MOVDN3` opcode `000_1101` (`b6..b0`). -/
def isMovdn3 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 opBit0)))))

/-- Canonical selector for the `MOVDN4` opcode `001_0001` (`b6..b0`). -/
def isMovdn4 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 opBit0)))))

/-- Canonical selector for the `MOVDN5` opcode `001_0011` (`b6..b0`). -/
def isMovdn5 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 opBit0)))))

/-- Canonical selector for the `MOVDN6` opcode `001_0101` (`b6..b0`). -/
def isMovdn6 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 opBit0)))))

/-- Canonical selector for the `MOVDN7` opcode `001_0111` (`b6..b0`). -/
def isMovdn7 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times opBit1 opBit0)))))

/-- Canonical selector for the `MOVDN8` opcode `001_1011` (`b6..b0`). -/
def isMovdn8 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 opBit0)))))

/-- Canonical selector for the `SWAPW` opcode `001_1000` (`b6..b0`). -/
def isSwapw : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for the `SWAPW2` opcode `001_1100` (`b6..b0`). -/
def isSwapw2 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for the `SWAPW3` opcode `001_1101` (`b6..b0`). -/
def isSwapw3 : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 opBit0)))))

/-- Canonical selector for the `SWAPDW` opcode `001_1110` (`b6..b0`). -/
def isSwapdw : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times opBit2
            (FExpr.times opBit1 notOpBit0)))))

/-- Canonical selector for the `CSWAP` opcode `010_1010` (`b6..b0`). -/
def isCswap : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 notOpBit0)))))

/-- Canonical selector for the `CSWAPW` opcode `010_1011` (`b6..b0`). -/
def isCswapw : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 opBit0)))))

/-- Canonical selector for the `CALLER` opcode `000_1001` (`b6..b0`). -/
def isCaller : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 opBit0)))))

/-- Canonical selector for the `SDEPTH` opcode `011_1101` (`b6..b0`). -/
def isSdepth : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 opBit0)))))

/-- Canonical AIR constraint for `MOVUP2`. -/
def movup2 : BaseConstraint :=
  whenTransition <| gate isMovup2 <| assertEq s0Next s2

/-- Canonical AIR constraint for `MOVUP3`. -/
def movup3 : BaseConstraint :=
  whenTransition <| gate isMovup3 <| assertEq s0Next s3

/-- Canonical AIR constraint for `MOVUP4`. -/
def movup4 : BaseConstraint :=
  whenTransition <| gate isMovup4 <| assertEq s0Next s4

/-- Canonical AIR constraint for `MOVUP5`. -/
def movup5 : BaseConstraint :=
  whenTransition <| gate isMovup5 <| assertEq s0Next s5

/-- Canonical AIR constraint for `MOVUP6`. -/
def movup6 : BaseConstraint :=
  whenTransition <| gate isMovup6 <| assertEq s0Next s6

/-- Canonical AIR constraint for `MOVUP7`. -/
def movup7 : BaseConstraint :=
  whenTransition <| gate isMovup7 <| assertEq s0Next s7

/-- Canonical AIR constraint for `MOVUP8`. -/
def movup8 : BaseConstraint :=
  whenTransition <| gate isMovup8 <| assertEq s0Next s8

/-- Canonical AIR constraint for `MOVDN2`. -/
def movdn2 : BaseConstraint :=
  whenTransition <| gate isMovdn2 <| assertEq s2Next s0

/-- Canonical AIR constraint for `MOVDN3`. -/
def movdn3 : BaseConstraint :=
  whenTransition <| gate isMovdn3 <| assertEq s3Next s0

/-- Canonical AIR constraint for `MOVDN4`. -/
def movdn4 : BaseConstraint :=
  whenTransition <| gate isMovdn4 <| assertEq s4Next s0

/-- Canonical AIR constraint for `MOVDN5`. -/
def movdn5 : BaseConstraint :=
  whenTransition <| gate isMovdn5 <| assertEq s5Next s0

/-- Canonical AIR constraint for `MOVDN6`. -/
def movdn6 : BaseConstraint :=
  whenTransition <| gate isMovdn6 <| assertEq s6Next s0

/-- Canonical AIR constraint for `MOVDN7`. -/
def movdn7 : BaseConstraint :=
  whenTransition <| gate isMovdn7 <| assertEq s7Next s0

/-- Canonical AIR constraint for `MOVDN8`. -/
def movdn8 : BaseConstraint :=
  whenTransition <| gate isMovdn8 <| assertEq s8Next s0

/-- Canonical AIR constraint for `SWAPW` on `s0'`. -/
def swapw0 : BaseConstraint :=
  whenTransition <| gate isSwapw <| assertEq s0Next s4

/-- Canonical AIR constraint for `SWAPW` on `s1'`. -/
def swapw1 : BaseConstraint :=
  whenTransition <| gate isSwapw <| assertEq s1Next s5

/-- Canonical AIR constraint for `SWAPW` on `s2'`. -/
def swapw2 : BaseConstraint :=
  whenTransition <| gate isSwapw <| assertEq s2Next s6

/-- Canonical AIR constraint for `SWAPW` on `s3'`. -/
def swapw3 : BaseConstraint :=
  whenTransition <| gate isSwapw <| assertEq s3Next s7

/-- Canonical AIR constraint for `SWAPW` on `s4'`. -/
def swapw4 : BaseConstraint :=
  whenTransition <| gate isSwapw <| assertEq s4Next s0

/-- Canonical AIR constraint for `SWAPW` on `s5'`. -/
def swapw5 : BaseConstraint :=
  whenTransition <| gate isSwapw <| assertEq s5Next s1

/-- Canonical AIR constraint for `SWAPW` on `s6'`. -/
def swapw6 : BaseConstraint :=
  whenTransition <| gate isSwapw <| assertEq s6Next s2

/-- Canonical AIR constraint for `SWAPW` on `s7'`. -/
def swapw7 : BaseConstraint :=
  whenTransition <| gate isSwapw <| assertEq s7Next s3

/-- Canonical AIR constraint for `SWAPW2` on `s0'`. -/
def swapw20 : BaseConstraint :=
  whenTransition <| gate isSwapw2 <| assertEq s0Next s8

/-- Canonical AIR constraint for `SWAPW2` on `s1'`. -/
def swapw21 : BaseConstraint :=
  whenTransition <| gate isSwapw2 <| assertEq s1Next s9

/-- Canonical AIR constraint for `SWAPW2` on `s2'`. -/
def swapw22 : BaseConstraint :=
  whenTransition <| gate isSwapw2 <| assertEq s2Next s10

/-- Canonical AIR constraint for `SWAPW2` on `s3'`. -/
def swapw23 : BaseConstraint :=
  whenTransition <| gate isSwapw2 <| assertEq s3Next s11

/-- Canonical AIR constraint for `SWAPW2` on `s8'`. -/
def swapw24 : BaseConstraint :=
  whenTransition <| gate isSwapw2 <| assertEq s8Next s0

/-- Canonical AIR constraint for `SWAPW2` on `s9'`. -/
def swapw25 : BaseConstraint :=
  whenTransition <| gate isSwapw2 <| assertEq s9Next s1

/-- Canonical AIR constraint for `SWAPW2` on `s10'`. -/
def swapw26 : BaseConstraint :=
  whenTransition <| gate isSwapw2 <| assertEq s10Next s2

/-- Canonical AIR constraint for `SWAPW2` on `s11'`. -/
def swapw27 : BaseConstraint :=
  whenTransition <| gate isSwapw2 <| assertEq s11Next s3

/-- Canonical AIR constraint for `SWAPW3` on `s0'`. -/
def swapw30 : BaseConstraint :=
  whenTransition <| gate isSwapw3 <| assertEq s0Next s12

/-- Canonical AIR constraint for `SWAPW3` on `s1'`. -/
def swapw31 : BaseConstraint :=
  whenTransition <| gate isSwapw3 <| assertEq s1Next s13

/-- Canonical AIR constraint for `SWAPW3` on `s2'`. -/
def swapw32 : BaseConstraint :=
  whenTransition <| gate isSwapw3 <| assertEq s2Next s14

/-- Canonical AIR constraint for `SWAPW3` on `s3'`. -/
def swapw33 : BaseConstraint :=
  whenTransition <| gate isSwapw3 <| assertEq s3Next s15

/-- Canonical AIR constraint for `SWAPW3` on `s12'`. -/
def swapw34 : BaseConstraint :=
  whenTransition <| gate isSwapw3 <| assertEq s12Next s0

/-- Canonical AIR constraint for `SWAPW3` on `s13'`. -/
def swapw35 : BaseConstraint :=
  whenTransition <| gate isSwapw3 <| assertEq s13Next s1

/-- Canonical AIR constraint for `SWAPW3` on `s14'`. -/
def swapw36 : BaseConstraint :=
  whenTransition <| gate isSwapw3 <| assertEq s14Next s2

/-- Canonical AIR constraint for `SWAPW3` on `s15'`. -/
def swapw37 : BaseConstraint :=
  whenTransition <| gate isSwapw3 <| assertEq s15Next s3

/-- Canonical AIR constraint for `SWAPDW` on `s0'`. -/
def swapdw0 : BaseConstraint :=
  whenTransition <| gate isSwapdw <| assertEq s0Next s8

/-- Canonical AIR constraint for `SWAPDW` on `s1'`. -/
def swapdw1 : BaseConstraint :=
  whenTransition <| gate isSwapdw <| assertEq s1Next s9

/-- Canonical AIR constraint for `SWAPDW` on `s2'`. -/
def swapdw2 : BaseConstraint :=
  whenTransition <| gate isSwapdw <| assertEq s2Next s10

/-- Canonical AIR constraint for `SWAPDW` on `s3'`. -/
def swapdw3 : BaseConstraint :=
  whenTransition <| gate isSwapdw <| assertEq s3Next s11

/-- Canonical AIR constraint for `SWAPDW` on `s4'`. -/
def swapdw4 : BaseConstraint :=
  whenTransition <| gate isSwapdw <| assertEq s4Next s12

/-- Canonical AIR constraint for `SWAPDW` on `s5'`. -/
def swapdw5 : BaseConstraint :=
  whenTransition <| gate isSwapdw <| assertEq s5Next s13

/-- Canonical AIR constraint for `SWAPDW` on `s6'`. -/
def swapdw6 : BaseConstraint :=
  whenTransition <| gate isSwapdw <| assertEq s6Next s14

/-- Canonical AIR constraint for `SWAPDW` on `s7'`. -/
def swapdw7 : BaseConstraint :=
  whenTransition <| gate isSwapdw <| assertEq s7Next s15

/-- Canonical AIR constraint for `SWAPDW` on `s8'`. -/
def swapdw8 : BaseConstraint :=
  whenTransition <| gate isSwapdw <| assertEq s8Next s0

/-- Canonical AIR constraint for `SWAPDW` on `s9'`. -/
def swapdw9 : BaseConstraint :=
  whenTransition <| gate isSwapdw <| assertEq s9Next s1

/-- Canonical AIR constraint for `SWAPDW` on `s10'`. -/
def swapdw10 : BaseConstraint :=
  whenTransition <| gate isSwapdw <| assertEq s10Next s2

/-- Canonical AIR constraint for `SWAPDW` on `s11'`. -/
def swapdw11 : BaseConstraint :=
  whenTransition <| gate isSwapdw <| assertEq s11Next s3

/-- Canonical AIR constraint for `SWAPDW` on `s12'`. -/
def swapdw12 : BaseConstraint :=
  whenTransition <| gate isSwapdw <| assertEq s12Next s4

/-- Canonical AIR constraint for `SWAPDW` on `s13'`. -/
def swapdw13 : BaseConstraint :=
  whenTransition <| gate isSwapdw <| assertEq s13Next s5

/-- Canonical AIR constraint for `SWAPDW` on `s14'`. -/
def swapdw14 : BaseConstraint :=
  whenTransition <| gate isSwapdw <| assertEq s14Next s6

/-- Canonical AIR constraint for `SWAPDW` on `s15'`. -/
def swapdw15 : BaseConstraint :=
  whenTransition <| gate isSwapdw <| assertEq s15Next s7

/-- Canonical AIR integrity constraint for `CSWAP` selector bitness. -/
def cswapBit : BaseConstraint :=
  gate isCswap <| assertZero <| FExpr.times s0 (FExpr.minus s0 (FExpr.const 1))

/-- Canonical AIR constraint for `CSWAP` on `s0'`. -/
def cswap0 : BaseConstraint :=
  whenTransition <| gate isCswap <|
    assertEq s0Next
      (FExpr.plus (FExpr.times s0 s2) (FExpr.times (FExpr.minus (FExpr.const 1) s0) s1))

/-- Canonical AIR constraint for `CSWAP` on `s1'`. -/
def cswap1 : BaseConstraint :=
  whenTransition <| gate isCswap <|
    assertEq s1Next
      (FExpr.plus (FExpr.times s0 s1) (FExpr.times (FExpr.minus (FExpr.const 1) s0) s2))

/-- Canonical AIR integrity constraint for `CSWAPW` selector bitness. -/
def cswapwBit : BaseConstraint :=
  gate isCswapw <| assertZero <| FExpr.times s0 (FExpr.minus s0 (FExpr.const 1))

/-- Canonical AIR constraint for `CSWAPW` on `s0'`. -/
def cswapw0 : BaseConstraint :=
  whenTransition <| gate isCswapw <|
    assertEq s0Next
      (FExpr.plus (FExpr.times s0 s5) (FExpr.times (FExpr.minus (FExpr.const 1) s0) s1))

/-- Canonical AIR constraint for `CSWAPW` on `s1'`. -/
def cswapw1 : BaseConstraint :=
  whenTransition <| gate isCswapw <|
    assertEq s1Next
      (FExpr.plus (FExpr.times s0 s6) (FExpr.times (FExpr.minus (FExpr.const 1) s0) s2))

/-- Canonical AIR constraint for `CSWAPW` on `s2'`. -/
def cswapw2 : BaseConstraint :=
  whenTransition <| gate isCswapw <|
    assertEq s2Next
      (FExpr.plus (FExpr.times s0 s7) (FExpr.times (FExpr.minus (FExpr.const 1) s0) s3))

/-- Canonical AIR constraint for `CSWAPW` on `s3'`. -/
def cswapw3 : BaseConstraint :=
  whenTransition <| gate isCswapw <|
    assertEq s3Next
      (FExpr.plus (FExpr.times s0 s8) (FExpr.times (FExpr.minus (FExpr.const 1) s0) s4))

/-- Canonical AIR constraint for `CSWAPW` on `s4'`. -/
def cswapw4 : BaseConstraint :=
  whenTransition <| gate isCswapw <|
    assertEq s4Next
      (FExpr.plus (FExpr.times s0 s1) (FExpr.times (FExpr.minus (FExpr.const 1) s0) s5))

/-- Canonical AIR constraint for `CSWAPW` on `s5'`. -/
def cswapw5 : BaseConstraint :=
  whenTransition <| gate isCswapw <|
    assertEq s5Next
      (FExpr.plus (FExpr.times s0 s2) (FExpr.times (FExpr.minus (FExpr.const 1) s0) s6))

/-- Canonical AIR constraint for `CSWAPW` on `s6'`. -/
def cswapw6 : BaseConstraint :=
  whenTransition <| gate isCswapw <|
    assertEq s6Next
      (FExpr.plus (FExpr.times s0 s3) (FExpr.times (FExpr.minus (FExpr.const 1) s0) s7))

/-- Canonical AIR constraint for `CSWAPW` on `s7'`. -/
def cswapw7 : BaseConstraint :=
  whenTransition <| gate isCswapw <|
    assertEq s7Next
      (FExpr.plus (FExpr.times s0 s4) (FExpr.times (FExpr.minus (FExpr.const 1) s0) s8))

/-- Canonical AIR constraint for `CALLER` on `s0'`. -/
def caller0 : BaseConstraint :=
  whenTransition <| gate isCaller <| assertEq s0Next fnHash0

/-- Canonical AIR constraint for `CALLER` on `s1'`. -/
def caller1 : BaseConstraint :=
  whenTransition <| gate isCaller <| assertEq s1Next fnHash1

/-- Canonical AIR constraint for `CALLER` on `s2'`. -/
def caller2 : BaseConstraint :=
  whenTransition <| gate isCaller <| assertEq s2Next fnHash2

/-- Canonical AIR constraint for `CALLER` on `s3'`. -/
def caller3 : BaseConstraint :=
  whenTransition <| gate isCaller <| assertEq s3Next fnHash3

/-- Canonical AIR constraint for `SDEPTH`. -/
def sdepth : BaseConstraint :=
  whenTransition <| gate isSdepth <| assertEq s0Next stackDepth

/-- Step 10 bounded-slice canonical `StackOps` base constraints. -/
def base : BaseConstraintSet := allOf
  [pad, dup0, dup1, dup2, dup3, dup4, dup5, dup6, dup7, dup9, dup11, dup13,
   dup15, clk, swap0, swap1, assertOne, movup2, movup3, movup4, movup5,
   movup6, movup7, movup8, movdn2, movdn3, movdn4, movdn5, movdn6, movdn7,
   movdn8, swapw0, swapw1, swapw2, swapw3, swapw4, swapw5, swapw6, swapw7,
   swapw20, swapw21, swapw22, swapw23, swapw24, swapw25, swapw26, swapw27,
   swapw30, swapw31, swapw32, swapw33, swapw34, swapw35, swapw36, swapw37,
   swapdw0, swapdw1, swapdw2, swapdw3, swapdw4, swapdw5, swapdw6, swapdw7,
   swapdw8, swapdw9, swapdw10, swapdw11, swapdw12, swapdw13, swapdw14,
   swapdw15, cswapBit, cswap0, cswap1, cswapwBit, cswapw0, cswapw1, cswapw2,
   cswapw3, cswapw4, cswapw5, cswapw6, cswapw7, caller0, caller1, caller2,
   caller3, sdepth]

private def padCurr (j : MainCol) : Felt :=
  match j.val with
  | 11 => 1
  | 12 => 1
  | _ => 0

private def goodPadNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 0
  | _ => 0

private def badPadNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 1
  | _ => 0

private def goodPadRow : AirRow := {
  curr := padCurr
  next := goodPadNext
  isTransition := 1
}

private def badPadRow : AirRow := {
  curr := padCurr
  next := badPadNext
  isTransition := 1
}

private def swapCurr (j : MainCol) : Felt :=
  match j.val with
  | 10 => 1
  | 30 => 3
  | 31 => 4
  | _ => 0

private def goodSwapNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 4
  | 31 => 3
  | _ => 0

private def badSwapNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 4
  | 31 => 4
  | _ => 0

private def goodSwapRow : AirRow := {
  curr := swapCurr
  next := goodSwapNext
  isTransition := 1
}

private def badSwapRow : AirRow := {
  curr := swapCurr
  next := badSwapNext
  isTransition := 1
}

private def cswapCurr (j : MainCol) : Felt :=
  match j.val with
  | 8 => 1
  | 10 => 1
  | 12 => 1
  | 30 => 1
  | 31 => 3
  | 32 => 5
  | _ => 0

private def goodCswapNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 5
  | 31 => 3
  | _ => 0

private def badCswapNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 3
  | 31 => 5
  | _ => 0

private def goodCswapRow : AirRow := {
  curr := cswapCurr
  next := goodCswapNext
  isTransition := 1
}

private def badCswapRow : AirRow := {
  curr := cswapCurr
  next := badCswapNext
  isTransition := 1
}

#eval checkBase goodPadRow base
#eval checkBase badPadRow base
#eval checkBase goodSwapRow base
#eval checkBase badSwapRow base
#eval checkBase goodCswapRow base
#eval checkBase badCswapRow base

end MidenLean.AIR.Semantics.Subsystems.StackOps
