import MidenLean.AIR.Semantics.Check
/-!
# Stack General AIR Implementation Layer

This file encodes the canonical visible-stack transition slice backed by
`air/src/constraints/stack/general/mod.rs`.

The Rust AIR derives the composite selectors `no_shift_at`, `left_shift_at`,
and `right_shift_at` from the reduced-degree `OpFlags` layer. This module
mirrors that bridge exactly, including the low-degree decoder extra columns
(`e0`, `e1`) and the loop-end helper flag (`h5` / column `19`), so the
structural 16 visible-stack constraints can refine directly to the extracted
symbolic AIR.
-/

namespace MidenLean.AIR.Semantics.Subsystems.StackGeneral

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder
open MidenLean.AIR.Semantics.Check

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
/-- Current-row decoder loop-end helper `h5` (`col 19`). -/
def loopFlagCol : MainCol := ⟨19, by decide⟩
/-- Current-row decoder extra column `e0` (`col 28`). -/
def extra0Col : MainCol := ⟨28, by decide⟩
/-- Current-row decoder extra column `e1` (`col 29`). -/
def extra1Col : MainCol := ⟨29, by decide⟩

/-- Current-row visible-stack top `s0`. -/
def s0 : FExpr := FExpr.curr s0Col
/-- Current-row visible-stack `s1`. -/
def s1 : FExpr := FExpr.curr s1Col
/-- Current-row visible-stack `s2`. -/
def s2 : FExpr := FExpr.curr s2Col
/-- Current-row visible-stack `s3`. -/
def s3 : FExpr := FExpr.curr s3Col
/-- Current-row visible-stack `s4`. -/
def s4 : FExpr := FExpr.curr s4Col
/-- Current-row visible-stack `s5`. -/
def s5 : FExpr := FExpr.curr s5Col
/-- Current-row visible-stack `s6`. -/
def s6 : FExpr := FExpr.curr s6Col
/-- Current-row visible-stack `s7`. -/
def s7 : FExpr := FExpr.curr s7Col
/-- Current-row visible-stack `s8`. -/
def s8 : FExpr := FExpr.curr s8Col
/-- Current-row visible-stack `s9`. -/
def s9 : FExpr := FExpr.curr s9Col
/-- Current-row visible-stack `s10`. -/
def s10 : FExpr := FExpr.curr s10Col
/-- Current-row visible-stack `s11`. -/
def s11 : FExpr := FExpr.curr s11Col
/-- Current-row visible-stack `s12`. -/
def s12 : FExpr := FExpr.curr s12Col
/-- Current-row visible-stack `s13`. -/
def s13 : FExpr := FExpr.curr s13Col
/-- Current-row visible-stack `s14`. -/
def s14 : FExpr := FExpr.curr s14Col
/-- Current-row visible-stack tail `s15`. -/
def s15 : FExpr := FExpr.curr s15Col

/-- Current-row decoder opcode bit `b0`. -/
def opBit0 : FExpr := FExpr.curr opBit0Col
/-- Current-row decoder opcode bit `b1`. -/
def opBit1 : FExpr := FExpr.curr opBit1Col
/-- Current-row decoder opcode bit `b2`. -/
def opBit2 : FExpr := FExpr.curr opBit2Col
/-- Current-row decoder opcode bit `b3`. -/
def opBit3 : FExpr := FExpr.curr opBit3Col
/-- Current-row decoder opcode bit `b4`. -/
def opBit4 : FExpr := FExpr.curr opBit4Col
/-- Current-row decoder opcode bit `b5`. -/
def opBit5 : FExpr := FExpr.curr opBit5Col
/-- Current-row decoder opcode bit `b6`. -/
def opBit6 : FExpr := FExpr.curr opBit6Col
/-- Current-row decoder loop-end helper `h5`. -/
def loopFlag : FExpr := FExpr.curr loopFlagCol
/-- Current-row decoder extra column `e0`. -/
def extra0 : FExpr := FExpr.curr extra0Col
/-- Current-row decoder extra column `e1`. -/
def extra1 : FExpr := FExpr.curr extra1Col

/-- Canonical `1 - b0`. -/
def notOpBit0 : FExpr := FExpr.minus (FExpr.const 1) opBit0
/-- Canonical `1 - b1`. -/
def notOpBit1 : FExpr := FExpr.minus (FExpr.const 1) opBit1
/-- Canonical `1 - b2`. -/
def notOpBit2 : FExpr := FExpr.minus (FExpr.const 1) opBit2
/-- Canonical `1 - b3`. -/
def notOpBit3 : FExpr := FExpr.minus (FExpr.const 1) opBit3
/-- Canonical `1 - b4`. -/
def notOpBit4 : FExpr := FExpr.minus (FExpr.const 1) opBit4
/-- Canonical `1 - b5`. -/
def notOpBit5 : FExpr := FExpr.minus (FExpr.const 1) opBit5
/-- Canonical `1 - b6`. -/
def notOpBit6 : FExpr := FExpr.minus (FExpr.const 1) opBit6

/-- Next-row visible-stack top `s0'`. -/
def s0Next : FExpr := FExpr.next s0Col
/-- Next-row visible-stack `s1'`. -/
def s1Next : FExpr := FExpr.next s1Col
/-- Next-row visible-stack `s2'`. -/
def s2Next : FExpr := FExpr.next s2Col
/-- Next-row visible-stack `s3'`. -/
def s3Next : FExpr := FExpr.next s3Col
/-- Next-row visible-stack `s4'`. -/
def s4Next : FExpr := FExpr.next s4Col
/-- Next-row visible-stack `s5'`. -/
def s5Next : FExpr := FExpr.next s5Col
/-- Next-row visible-stack `s6'`. -/
def s6Next : FExpr := FExpr.next s6Col
/-- Next-row visible-stack `s7'`. -/
def s7Next : FExpr := FExpr.next s7Col
/-- Next-row visible-stack `s8'`. -/
def s8Next : FExpr := FExpr.next s8Col
/-- Next-row visible-stack `s9'`. -/
def s9Next : FExpr := FExpr.next s9Col
/-- Next-row visible-stack `s10'`. -/
def s10Next : FExpr := FExpr.next s10Col
/-- Next-row visible-stack `s11'`. -/
def s11Next : FExpr := FExpr.next s11Col
/-- Next-row visible-stack `s12'`. -/
def s12Next : FExpr := FExpr.next s12Col
/-- Next-row visible-stack `s13'`. -/
def s13Next : FExpr := FExpr.next s13Col
/-- Next-row visible-stack `s14'`. -/
def s14Next : FExpr := FExpr.next s14Col
/-- Next-row visible-stack tail `s15'`. -/
def s15Next : FExpr := FExpr.next s15Col

/-- Zero expression used for the missing source on boundary stack slots. -/
def zero : FExpr := FExpr.const 0

/-- Symbolic composite shift selectors for the 16 visible stack positions. -/
structure ShiftFlags where
  noShift : Fin 16 → FExpr
  leftShift : Fin 16 → FExpr
  rightShift : Fin 16 → FExpr

/-- Sum of the selectors active for one visible stack position. -/
def flagSum (noShift leftShiftUp rightShiftDn : FExpr) : FExpr :=
  FExpr.plus noShift (FExpr.plus leftShiftUp rightShiftDn)

/-- Expected current-row source contribution for one visible stack position. -/
def expectedValue (noShift leftShiftUp rightShiftDn si siPlus siMinus : FExpr) : FExpr :=
  FExpr.plus
    (FExpr.times noShift si)
    (FExpr.plus
      (FExpr.times leftShiftUp siPlus)
      (FExpr.times rightShiftDn siMinus))

/-- Canonical structural stack-transition law for one visible position.

The index is documentary only; position `0` passes `0` for the missing
right-shift source, and position `15` passes `0` for the missing left-shift
source. -/
def stackTransition (_i : Nat) (noShift leftShiftUp rightShiftDn : FExpr)
    (si siNext siPlus siMinus : FExpr) : BaseConstraint :=
  let activeFlags := flagSum noShift leftShiftUp rightShiftDn
  let expected := expectedValue noShift leftShiftUp rightShiftDn si siPlus siMinus
  whenTransition <| assertZero <|
    FExpr.minus (FExpr.times siNext activeFlags) expected

/-- Pick either a decoder bit or its complement according to a Boolean literal. -/
def pickBit (bit notBit : FExpr) (takeBit : Bool) : FExpr :=
  if takeBit then bit else notBit

/-- Exact degree-7 selector builder for the `b6 = 0` opcode block. -/
def degree7Flag (b5 b4 b3 b2 b1 b0 : Bool) : FExpr :=
  FExpr.times notOpBit6 <|
    FExpr.times (pickBit opBit5 notOpBit5 b5) <|
      FExpr.times (pickBit opBit4 notOpBit4 b4) <|
        FExpr.times (pickBit opBit3 notOpBit3 b3) <|
          FExpr.times (pickBit opBit2 notOpBit2 b2) <|
            FExpr.times (pickBit opBit1 notOpBit1 b1) <|
              pickBit opBit0 notOpBit0 b0

/-- Exact degree-7 selector builder with the least significant opcode bit omitted. -/
def degree7PairFlag (b5 b4 b3 b2 b1 : Bool) : FExpr :=
  FExpr.times notOpBit6 <|
    FExpr.times (pickBit opBit5 notOpBit5 b5) <|
      FExpr.times (pickBit opBit4 notOpBit4 b4) <|
        FExpr.times (pickBit opBit3 notOpBit3 b3) <|
          FExpr.times (pickBit opBit2 notOpBit2 b2) <|
            pickBit opBit1 notOpBit1 b1

/-- Exact degree-6 selector builder for the `100_xxx?` `u32` block. -/
def degree6Flag (b3 b2 b1 : Bool) : FExpr :=
  FExpr.times opBit6 <|
    FExpr.times notOpBit5 <|
      FExpr.times notOpBit4 <|
        FExpr.times (pickBit opBit3 notOpBit3 b3) <|
          FExpr.times (pickBit opBit2 notOpBit2 b2) <|
            pickBit opBit1 notOpBit1 b1

/-- Exact degree-5 selector builder using decoder extra column `e0`. -/
def degree5Flag (b3 b2 b1 b0 : Bool) : FExpr :=
  FExpr.times extra0 <|
    FExpr.times (pickBit opBit3 notOpBit3 b3) <|
      FExpr.times (pickBit opBit2 notOpBit2 b2) <|
        FExpr.times (pickBit opBit1 notOpBit1 b1) <|
          pickBit opBit0 notOpBit0 b0

/-- Exact degree-4 selector builder using decoder extra column `e1`. -/
def degree4Flag (b4 b3 b2 : Bool) : FExpr :=
  FExpr.times extra1 <|
    FExpr.times (pickBit opBit4 notOpBit4 b4) <|
      FExpr.times (pickBit opBit3 notOpBit3 b3) <|
        pickBit opBit2 notOpBit2 b2

/-- Low-degree prefix `010` used by Rust's aggregate left-shift bridge. -/
def prefix010 : FExpr :=
  FExpr.times notOpBit6 <| FExpr.times opBit5 notOpBit4

/-- Low-degree prefix `011` used by Rust's aggregate right-shift bridge. -/
def prefix011 : FExpr :=
  FExpr.times notOpBit6 <| FExpr.times opBit5 opBit4

/-- Degree-4 prefix `0000` used to derive `no_change_1_flag`. -/
def prefix0000 : FExpr :=
  FExpr.times notOpBit6 <| FExpr.times notOpBit5 <| FExpr.times notOpBit4 notOpBit3

/-- Degree-4 prefix `0100` used to derive `left_change_1_flag`. -/
def prefix0100 : FExpr :=
  FExpr.times notOpBit6 <| FExpr.times opBit5 <| FExpr.times notOpBit4 notOpBit3

/-- Degree-4 prefix `1000` covering all reduced-degree `u32` arithmetic flags. -/
def prefix1000 : FExpr :=
  FExpr.times opBit6 <| FExpr.times notOpBit5 <| FExpr.times notOpBit4 notOpBit3

/-- Degree-5 prefix shared by `U32ADD3` and `U32MADD`. -/
def prefixAdd3Madd : FExpr :=
  FExpr.times opBit6 <|
    FExpr.times notOpBit5 <| FExpr.times notOpBit4 <| FExpr.times opBit3 opBit2

def flagNoop : FExpr := degree7Flag false false false false false false
def flagSwap : FExpr := degree7Flag false false true false false false
def flagEmit : FExpr := degree7Flag false true true true true true
def flagAssert : FExpr := degree7Flag true false false false false false
def flagSwapw : FExpr := degree7Flag false true true false false false
def flagExt2Mul : FExpr := degree7Flag false true true false false true
def flagDrop : FExpr := degree7Flag true false true false false true
def flagCswap : FExpr := degree7Flag true false true false true false
def flagCswapw : FExpr := degree7Flag true false true false true true
def flagMloadw : FExpr := degree7Flag true false true true false false
def flagMstore : FExpr := degree7Flag true false true true false true
def flagMstorew : FExpr := degree7Flag true false true true true false
def flagUnused47 : FExpr := degree7Flag true false true true true true

def flagMov2 : FExpr := degree7PairFlag false false true false true
def flagMov3 : FExpr := degree7PairFlag false false true true false
def flagMov4 : FExpr := degree7PairFlag false true false false false
def flagMov5 : FExpr := degree7PairFlag false true false false true
def flagMov6 : FExpr := degree7PairFlag false true false true false
def flagMov7 : FExpr := degree7PairFlag false true false true true
def flagMov8 : FExpr := degree7PairFlag false true true false true
def flagSwapwx : FExpr := degree7PairFlag false true true true false
def flagAdvPopwExpacc : FExpr := degree7PairFlag false false true true true

def flagMovup2 : FExpr := FExpr.times flagMov2 notOpBit0
def flagMovdn2 : FExpr := FExpr.times flagMov2 opBit0
def flagMovup3 : FExpr := FExpr.times flagMov3 notOpBit0
def flagMovdn3 : FExpr := FExpr.times flagMov3 opBit0
def flagMovup4 : FExpr := FExpr.times flagMov4 notOpBit0
def flagMovdn4 : FExpr := FExpr.times flagMov4 opBit0
def flagMovup5 : FExpr := FExpr.times flagMov5 notOpBit0
def flagMovdn5 : FExpr := FExpr.times flagMov5 opBit0
def flagMovup6 : FExpr := FExpr.times flagMov6 notOpBit0
def flagMovdn6 : FExpr := FExpr.times flagMov6 opBit0
def flagMovup7 : FExpr := FExpr.times flagMov7 notOpBit0
def flagMovdn7 : FExpr := FExpr.times flagMov7 opBit0
def flagMovup8 : FExpr := FExpr.times flagMov8 notOpBit0
def flagMovdn8 : FExpr := FExpr.times flagMov8 opBit0
def flagSwapw2 : FExpr := FExpr.times flagSwapwx notOpBit0
def flagSwapw3 : FExpr := FExpr.times flagSwapwx opBit0

def flagU32Split : FExpr := degree6Flag true false false
def flagU32Assert2 : FExpr := degree6Flag true false true
def flagU32Add3 : FExpr := degree6Flag true true false
def flagU32Madd : FExpr := degree6Flag true true true

def flagHperm : FExpr := degree5Flag false false false false
def flagMpverify : FExpr := degree5Flag false false false true
def flagSplit : FExpr := degree5Flag false true false false
def flagLoop : FExpr := degree5Flag false true false true
def flagSpan : FExpr := degree5Flag false true true false
def flagJoin : FExpr := degree5Flag false true true true
def flagDyn : FExpr := degree5Flag true false false false
def flagPush : FExpr := degree5Flag true false true true
def flagDyncall : FExpr := degree5Flag true true false false

def flagMrupdate : FExpr := degree4Flag false false false
def flagCall : FExpr := degree4Flag false true true
def flagEnd : FExpr := degree4Flag true false false
def flagRepeat : FExpr := degree4Flag true false true
def flagRespan : FExpr := degree4Flag true true false
def flagHalt : FExpr := degree4Flag true true true

/-- Exact Rust aggregate `f0000 - noop`. -/
def flagNoChange1 : FExpr := FExpr.minus prefix0000 flagNoop

/-- Exact Rust aggregate `f0100 - assert`. -/
def flagLeftChange1 : FExpr := FExpr.minus prefix0100 flagAssert

/-- Sum of all visible `MOVDN.{2..8}` selectors. -/
def flagMovdnAll : FExpr :=
  FExpr.plus flagMovdn2 <| FExpr.plus flagMovdn3 <| FExpr.plus flagMovdn4 <|
    FExpr.plus flagMovdn5 <| FExpr.plus flagMovdn6 <|
      FExpr.plus flagMovdn7 flagMovdn8

/-- Sum of all visible `MOVUP.{2..8}` selectors. -/
def flagMovupAll : FExpr :=
  FExpr.plus flagMovup2 <| FExpr.plus flagMovup3 <| FExpr.plus flagMovup4 <|
    FExpr.plus flagMovup5 <| FExpr.plus flagMovup6 <|
      FExpr.plus flagMovup7 flagMovup8

/-- Exact Rust aggregate `split + loop`. -/
def flagSplitLoop : FExpr := FExpr.plus flagSplit flagLoop

/-- Exact Rust aggregate `u32add3 + u32madd`. -/
def flagAdd3Madd : FExpr := FExpr.plus flagU32Add3 flagU32Madd

/-- Exact Rust aggregate `end * is_loop_end`. -/
def flagShiftLeftOnEnd : FExpr := FExpr.times flagEnd loopFlag

def noShift0 : FExpr :=
  FExpr.plus flagNoop <| FExpr.plus flagU32Assert2 <| FExpr.plus flagMpverify <|
    FExpr.plus flagSpan <| FExpr.plus flagJoin <| FExpr.plus flagEmit <|
      FExpr.plus flagRespan <| FExpr.plus flagHalt <| FExpr.plus flagCall <|
        FExpr.times flagEnd (FExpr.minus (FExpr.const 1) loopFlag)

def noShift1 : FExpr := FExpr.plus noShift0 flagNoChange1
def noShift2 : FExpr := FExpr.plus noShift1 <| FExpr.plus flagSwap prefix1000
def noShift3 : FExpr := FExpr.plus noShift2 flagMov2
def noShift4 : FExpr :=
  FExpr.plus noShift3 <| FExpr.plus flagMov3 <| FExpr.plus flagAdvPopwExpacc <|
    FExpr.plus flagSwapwx <| FExpr.plus flagExt2Mul flagMrupdate
def noShift5 : FExpr := FExpr.plus noShift4 flagMov4
def noShift6 : FExpr := FExpr.plus noShift5 flagMov5
def noShift7 : FExpr := FExpr.plus noShift6 flagMov6
def noShift8 : FExpr :=
  FExpr.plus noShift7 <| FExpr.plus flagMov7 <| FExpr.minus flagSwapw flagSwapw2
def noShift9 : FExpr := FExpr.plus noShift8 flagMov8
def noShift10 : FExpr := noShift9
def noShift11 : FExpr := noShift9
def noShift12 : FExpr :=
  FExpr.plus (FExpr.minus noShift9 flagSwapw3) <| FExpr.plus flagSwapw2 flagHperm
def noShift13 : FExpr := noShift12
def noShift14 : FExpr := noShift12
def noShift15 : FExpr := noShift12

def leftShift1 : FExpr :=
  FExpr.plus flagAssert <| FExpr.plus flagMovdnAll <| FExpr.plus flagDrop <|
    FExpr.plus flagMstore <| FExpr.plus flagUnused47 <| FExpr.plus flagMstorew <|
      FExpr.plus flagSplitLoop <| FExpr.plus flagShiftLeftOnEnd <|
        FExpr.plus flagDyn flagDyncall
def leftShift2 : FExpr := FExpr.plus leftShift1 flagLeftChange1
def leftShift3 : FExpr :=
  FExpr.plus leftShift2 <| FExpr.plus flagAdd3Madd (FExpr.minus flagCswap flagMovdn2)
def leftShift4 : FExpr := FExpr.minus leftShift3 flagMovdn3
def leftShift5 : FExpr := FExpr.plus leftShift4 (FExpr.minus flagMloadw flagMovdn4)
def leftShift6 : FExpr := FExpr.minus leftShift5 flagMovdn5
def leftShift7 : FExpr := FExpr.minus leftShift6 flagMovdn6
def leftShift8 : FExpr := FExpr.minus leftShift7 flagMovdn7
def leftShift9 : FExpr := FExpr.plus leftShift8 (FExpr.minus flagCswapw flagMovdn8)
def leftShift10 : FExpr := leftShift9
def leftShift11 : FExpr := leftShift9
def leftShift12 : FExpr := leftShift9
def leftShift13 : FExpr := leftShift9
def leftShift14 : FExpr := leftShift9
def leftShift15 : FExpr := leftShift9

def rightShift0 : FExpr := FExpr.plus prefix011 <| FExpr.plus flagPush flagMovupAll
def rightShift1 : FExpr := FExpr.plus rightShift0 flagU32Split
def rightShift2 : FExpr := FExpr.minus rightShift1 flagMovup2
def rightShift3 : FExpr := FExpr.minus rightShift2 flagMovup3
def rightShift4 : FExpr := FExpr.minus rightShift3 flagMovup4
def rightShift5 : FExpr := FExpr.minus rightShift4 flagMovup5
def rightShift6 : FExpr := FExpr.minus rightShift5 flagMovup6
def rightShift7 : FExpr := FExpr.minus rightShift6 flagMovup7
def rightShift8 : FExpr := FExpr.minus rightShift7 flagMovup8
def rightShift9 : FExpr := rightShift8
def rightShift10 : FExpr := rightShift8
def rightShift11 : FExpr := rightShift8
def rightShift12 : FExpr := rightShift8
def rightShift13 : FExpr := rightShift8
def rightShift14 : FExpr := rightShift8
def rightShift15 : FExpr := rightShift8

/-- Exact `OpFlags::no_shift_at` bridge from Rust `constraints/op_flags/mod.rs`. -/
def noShiftAt (i : Fin 16) : FExpr :=
  match i.1 with
  | 0 => noShift0
  | 1 => noShift1
  | 2 => noShift2
  | 3 => noShift3
  | 4 => noShift4
  | 5 => noShift5
  | 6 => noShift6
  | 7 => noShift7
  | 8 => noShift8
  | 9 => noShift9
  | 10 => noShift10
  | 11 => noShift11
  | 12 => noShift12
  | 13 => noShift13
  | 14 => noShift14
  | 15 => noShift15
  | _ => zero

/-- Exact `OpFlags::left_shift_at` bridge from Rust `constraints/op_flags/mod.rs`. -/
def leftShiftAt (i : Fin 16) : FExpr :=
  match i.1 with
  | 0 => zero
  | 1 => leftShift1
  | 2 => leftShift2
  | 3 => leftShift3
  | 4 => leftShift4
  | 5 => leftShift5
  | 6 => leftShift6
  | 7 => leftShift7
  | 8 => leftShift8
  | 9 => leftShift9
  | 10 => leftShift10
  | 11 => leftShift11
  | 12 => leftShift12
  | 13 => leftShift13
  | 14 => leftShift14
  | 15 => leftShift15
  | _ => zero

/-- Exact `OpFlags::right_shift_at` bridge from Rust `constraints/op_flags/mod.rs`. -/
def rightShiftAt (i : Fin 16) : FExpr :=
  match i.1 with
  | 0 => rightShift0
  | 1 => rightShift1
  | 2 => rightShift2
  | 3 => rightShift3
  | 4 => rightShift4
  | 5 => rightShift5
  | 6 => rightShift6
  | 7 => rightShift7
  | 8 => rightShift8
  | 9 => rightShift9
  | 10 => rightShift10
  | 11 => rightShift11
  | 12 => rightShift12
  | 13 => rightShift13
  | 14 => rightShift14
  | 15 => rightShift15
  | _ => zero

/-- Exact composite shift selectors mirrored from Rust `OpFlags`. -/
def exactFlags : ShiftFlags where
  noShift := noShiftAt
  leftShift := leftShiftAt
  rightShift := rightShiftAt

/-- Position-0 general stack transition.

This models `s0' * (noShift0 + leftShift1) = noShift0 * s0 + leftShift1 * s1`. -/
def transition0 (flags : ShiftFlags) : BaseConstraint :=
  stackTransition 0
    (flags.noShift ⟨0, by decide⟩)
    (flags.leftShift ⟨1, by decide⟩)
    zero
    s0 s0Next s1 zero

/-- Position-1 general stack transition. -/
def transition1 (flags : ShiftFlags) : BaseConstraint :=
  stackTransition 1
    (flags.noShift ⟨1, by decide⟩)
    (flags.leftShift ⟨2, by decide⟩)
    (flags.rightShift ⟨0, by decide⟩)
    s1 s1Next s2 s0

/-- Position-2 general stack transition. -/
def transition2 (flags : ShiftFlags) : BaseConstraint :=
  stackTransition 2
    (flags.noShift ⟨2, by decide⟩)
    (flags.leftShift ⟨3, by decide⟩)
    (flags.rightShift ⟨1, by decide⟩)
    s2 s2Next s3 s1

/-- Position-3 general stack transition. -/
def transition3 (flags : ShiftFlags) : BaseConstraint :=
  stackTransition 3
    (flags.noShift ⟨3, by decide⟩)
    (flags.leftShift ⟨4, by decide⟩)
    (flags.rightShift ⟨2, by decide⟩)
    s3 s3Next s4 s2

/-- Position-4 general stack transition. -/
def transition4 (flags : ShiftFlags) : BaseConstraint :=
  stackTransition 4
    (flags.noShift ⟨4, by decide⟩)
    (flags.leftShift ⟨5, by decide⟩)
    (flags.rightShift ⟨3, by decide⟩)
    s4 s4Next s5 s3

/-- Position-5 general stack transition. -/
def transition5 (flags : ShiftFlags) : BaseConstraint :=
  stackTransition 5
    (flags.noShift ⟨5, by decide⟩)
    (flags.leftShift ⟨6, by decide⟩)
    (flags.rightShift ⟨4, by decide⟩)
    s5 s5Next s6 s4

/-- Position-6 general stack transition. -/
def transition6 (flags : ShiftFlags) : BaseConstraint :=
  stackTransition 6
    (flags.noShift ⟨6, by decide⟩)
    (flags.leftShift ⟨7, by decide⟩)
    (flags.rightShift ⟨5, by decide⟩)
    s6 s6Next s7 s5

/-- Position-7 general stack transition. -/
def transition7 (flags : ShiftFlags) : BaseConstraint :=
  stackTransition 7
    (flags.noShift ⟨7, by decide⟩)
    (flags.leftShift ⟨8, by decide⟩)
    (flags.rightShift ⟨6, by decide⟩)
    s7 s7Next s8 s6

/-- Position-8 general stack transition. -/
def transition8 (flags : ShiftFlags) : BaseConstraint :=
  stackTransition 8
    (flags.noShift ⟨8, by decide⟩)
    (flags.leftShift ⟨9, by decide⟩)
    (flags.rightShift ⟨7, by decide⟩)
    s8 s8Next s9 s7

/-- Position-9 general stack transition. -/
def transition9 (flags : ShiftFlags) : BaseConstraint :=
  stackTransition 9
    (flags.noShift ⟨9, by decide⟩)
    (flags.leftShift ⟨10, by decide⟩)
    (flags.rightShift ⟨8, by decide⟩)
    s9 s9Next s10 s8

/-- Position-10 general stack transition. -/
def transition10 (flags : ShiftFlags) : BaseConstraint :=
  stackTransition 10
    (flags.noShift ⟨10, by decide⟩)
    (flags.leftShift ⟨11, by decide⟩)
    (flags.rightShift ⟨9, by decide⟩)
    s10 s10Next s11 s9

/-- Position-11 general stack transition. -/
def transition11 (flags : ShiftFlags) : BaseConstraint :=
  stackTransition 11
    (flags.noShift ⟨11, by decide⟩)
    (flags.leftShift ⟨12, by decide⟩)
    (flags.rightShift ⟨10, by decide⟩)
    s11 s11Next s12 s10

/-- Position-12 general stack transition. -/
def transition12 (flags : ShiftFlags) : BaseConstraint :=
  stackTransition 12
    (flags.noShift ⟨12, by decide⟩)
    (flags.leftShift ⟨13, by decide⟩)
    (flags.rightShift ⟨11, by decide⟩)
    s12 s12Next s13 s11

/-- Position-13 general stack transition. -/
def transition13 (flags : ShiftFlags) : BaseConstraint :=
  stackTransition 13
    (flags.noShift ⟨13, by decide⟩)
    (flags.leftShift ⟨14, by decide⟩)
    (flags.rightShift ⟨12, by decide⟩)
    s13 s13Next s14 s12

/-- Position-14 general stack transition. -/
def transition14 (flags : ShiftFlags) : BaseConstraint :=
  stackTransition 14
    (flags.noShift ⟨14, by decide⟩)
    (flags.leftShift ⟨15, by decide⟩)
    (flags.rightShift ⟨13, by decide⟩)
    s14 s14Next s15 s13

/-- Position-15 general stack transition.

This models
`s15' * (noShift15 + rightShift14) = noShift15 * s15 + rightShift14 * s14`. -/
def transition15 (flags : ShiftFlags) : BaseConstraint :=
  stackTransition 15
    (flags.noShift ⟨15, by decide⟩)
    zero
    (flags.rightShift ⟨14, by decide⟩)
    s15 s15Next zero s14

/-- Canonical general stack-transition constraints parameterized by the
composite shift-flag bridge. -/
def baseWith (flags : ShiftFlags) : BaseConstraintSet := allOf
  [ transition0 flags
  , transition1 flags
  , transition2 flags
  , transition3 flags
  , transition4 flags
  , transition5 flags
  , transition6 flags
  , transition7 flags
  , transition8 flags
  , transition9 flags
  , transition10 flags
  , transition11 flags
  , transition12 flags
  , transition13 flags
  , transition14 flags
  , transition15 flags
  ]

/-- Canonical general stack-transition constraints with the exact Rust-backed
composite shift flags. -/
def base : BaseConstraintSet := baseWith exactFlags

end MidenLean.AIR.Semantics.Subsystems.StackGeneral
