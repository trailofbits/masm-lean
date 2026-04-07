import MidenLean.AIR.Semantics.Check
/-!
# StackCrypto AIR Implementation Layer

This file mirrors `air/src/constraints/stack/crypto/mod.rs`.

The current Rust stack-crypto slice contains only `CRYPTOSTREAM`,
`HORNERBASE`, and `HORNEREXT`, for 46 base-field constraints total.
Memory, Merkle, and hasher operations grouped under "crypto" elsewhere are
handled in other AIR modules.

As in `StackOps`, selectors are written as raw 7-bit opcode tests rather than
with the decoder extra-column factorization.

Each transition rule follows the documented gated pattern

`is_transition * selector * body = 0`.

The helper-consistency rules inside `HORNERBASE` and `HORNEREXT` are integrity
rules, so their canonical form omits the transition factor.

Rust's `USER_OP_HELPERS_OFFSET` lands at global main-trace columns `16..21`,
so this file uses the same `uopH*` mapping as `StackArith`.
-/

namespace MidenLean.AIR.Semantics.Subsystems.StackCrypto

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder
open MidenLean.AIR.Semantics.Check

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

/-- Current-row user-op helper `h0` (`col 16`). -/
def uopH0Col : MainCol := ⟨16, by decide⟩
/-- Current-row user-op helper `h1` (`col 17`). -/
def uopH1Col : MainCol := ⟨17, by decide⟩
/-- Current-row user-op helper `h2` (`col 18`). -/
def uopH2Col : MainCol := ⟨18, by decide⟩
/-- Current-row user-op helper `h3` (`col 19`). -/
def uopH3Col : MainCol := ⟨19, by decide⟩
/-- Current-row user-op helper `h4` (`col 20`). -/
def uopH4Col : MainCol := ⟨20, by decide⟩
/-- Current-row user-op helper `h5` (`col 21`). -/
def uopH5Col : MainCol := ⟨21, by decide⟩

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

/-- Canonical `1 - x` helper. -/
def oneMinus (x : FExpr) : FExpr := FExpr.minus (FExpr.const 1) x

def notOpBit0 : FExpr := oneMinus opBit0
def notOpBit1 : FExpr := oneMinus opBit1
def notOpBit2 : FExpr := oneMinus opBit2
def notOpBit3 : FExpr := oneMinus opBit3
def notOpBit4 : FExpr := oneMinus opBit4
def notOpBit5 : FExpr := oneMinus opBit5
def notOpBit6 : FExpr := oneMinus opBit6

/-- Canonical current-row user-op helper `h0`. -/
def uopH0 : FExpr := FExpr.curr uopH0Col
/-- Canonical current-row user-op helper `h1`. -/
def uopH1 : FExpr := FExpr.curr uopH1Col
/-- Canonical current-row user-op helper `h2`. -/
def uopH2 : FExpr := FExpr.curr uopH2Col
/-- Canonical current-row user-op helper `h3`. -/
def uopH3 : FExpr := FExpr.curr uopH3Col
/-- Canonical current-row user-op helper `h4`. -/
def uopH4 : FExpr := FExpr.curr uopH4Col
/-- Canonical current-row user-op helper `h5`. -/
def uopH5 : FExpr := FExpr.curr uopH5Col

/-- Canonical current-row visible-stack `s0`. -/
def s0 : FExpr := FExpr.curr s0Col
/-- Canonical current-row visible-stack `s1`. -/
def s1 : FExpr := FExpr.curr s1Col
/-- Canonical current-row visible-stack `s2`. -/
def s2 : FExpr := FExpr.curr s2Col
/-- Canonical current-row visible-stack `s3`. -/
def s3 : FExpr := FExpr.curr s3Col
/-- Canonical current-row visible-stack `s4`. -/
def s4 : FExpr := FExpr.curr s4Col
/-- Canonical current-row visible-stack `s5`. -/
def s5 : FExpr := FExpr.curr s5Col
/-- Canonical current-row visible-stack `s6`. -/
def s6 : FExpr := FExpr.curr s6Col
/-- Canonical current-row visible-stack `s7`. -/
def s7 : FExpr := FExpr.curr s7Col
/-- Canonical current-row visible-stack `s8`. -/
def s8 : FExpr := FExpr.curr s8Col
/-- Canonical current-row visible-stack `s9`. -/
def s9 : FExpr := FExpr.curr s9Col
/-- Canonical current-row visible-stack `s10`. -/
def s10 : FExpr := FExpr.curr s10Col
/-- Canonical current-row visible-stack `s11`. -/
def s11 : FExpr := FExpr.curr s11Col
/-- Canonical current-row visible-stack `s12`. -/
def s12 : FExpr := FExpr.curr s12Col
/-- Canonical current-row visible-stack `s13`. -/
def s13 : FExpr := FExpr.curr s13Col
/-- Canonical current-row visible-stack `s14`. -/
def s14 : FExpr := FExpr.curr s14Col
/-- Canonical current-row visible-stack `s15`. -/
def s15 : FExpr := FExpr.curr s15Col

/-- Canonical next-row visible-stack `s0`. -/
def s0Next : FExpr := FExpr.next s0Col
/-- Canonical next-row visible-stack `s1`. -/
def s1Next : FExpr := FExpr.next s1Col
/-- Canonical next-row visible-stack `s2`. -/
def s2Next : FExpr := FExpr.next s2Col
/-- Canonical next-row visible-stack `s3`. -/
def s3Next : FExpr := FExpr.next s3Col
/-- Canonical next-row visible-stack `s4`. -/
def s4Next : FExpr := FExpr.next s4Col
/-- Canonical next-row visible-stack `s5`. -/
def s5Next : FExpr := FExpr.next s5Col
/-- Canonical next-row visible-stack `s6`. -/
def s6Next : FExpr := FExpr.next s6Col
/-- Canonical next-row visible-stack `s7`. -/
def s7Next : FExpr := FExpr.next s7Col
/-- Canonical next-row visible-stack `s8`. -/
def s8Next : FExpr := FExpr.next s8Col
/-- Canonical next-row visible-stack `s9`. -/
def s9Next : FExpr := FExpr.next s9Col
/-- Canonical next-row visible-stack `s10`. -/
def s10Next : FExpr := FExpr.next s10Col
/-- Canonical next-row visible-stack `s11`. -/
def s11Next : FExpr := FExpr.next s11Col
/-- Canonical next-row visible-stack `s12`. -/
def s12Next : FExpr := FExpr.next s12Col
/-- Canonical next-row visible-stack `s13`. -/
def s13Next : FExpr := FExpr.next s13Col
/-- Canonical next-row visible-stack `s14`. -/
def s14Next : FExpr := FExpr.next s14Col
/-- Canonical next-row visible-stack `s15`. -/
def s15Next : FExpr := FExpr.next s15Col

/-- Constant `7`, the quadratic-extension residue `u^2 = 7`. -/
def seven : FExpr := FExpr.const 7
/-- Constant `8`, the `CRYPTOSTREAM` counter increment. -/
def eight : FExpr := FExpr.const 8

/-- Canonical transition-gated equality constraint. -/
def transitionEq (selector lhs rhs : FExpr) : BaseConstraint :=
  whenTransition <| gate selector <| assertEq lhs rhs

/-- Canonical integrity-gated equality constraint. -/
def integrityEq (selector lhs rhs : FExpr) : BaseConstraint :=
  gate selector <| assertEq lhs rhs

/-- Real part of quadratic-extension multiplication with `u^2 = 7`. -/
def quadMulRe (a0 a1 b0 b1 : FExpr) : FExpr :=
  FExpr.plus (FExpr.times a0 b0) (FExpr.times seven (FExpr.times a1 b1))

/-- Imaginary part of quadratic-extension multiplication with `u^2 = 7`. -/
def quadMulIm (a0 a1 b0 b1 : FExpr) : FExpr :=
  FExpr.plus (FExpr.times a0 b1) (FExpr.times a1 b0)

/-- Real part of quadratic-extension squaring with `u^2 = 7`. -/
def quadSquareRe (a0 a1 : FExpr) : FExpr :=
  FExpr.plus (FExpr.times a0 a0) (FExpr.times seven (FExpr.times a1 a1))

/-- Imaginary part of quadratic-extension squaring with `u^2 = 7`. -/
def quadSquareIm (a0 a1 : FExpr) : FExpr :=
  FExpr.plus (FExpr.times a0 a1) (FExpr.times a0 a1)

/-- Shared `alpha.0` helper used by both Horner ops. -/
def alpha0 : FExpr := uopH0
/-- Shared `alpha.1` helper used by both Horner ops. -/
def alpha1 : FExpr := uopH1

/-- Shared `alpha^2` real component. -/
def alpha2Re : FExpr := quadSquareRe alpha0 alpha1
/-- Shared `alpha^2` imaginary component. -/
def alpha2Im : FExpr := quadSquareIm alpha0 alpha1
/-- Shared `alpha^3` real component. -/
def alpha3Re : FExpr := quadMulRe alpha2Re alpha2Im alpha0 alpha1
/-- Shared `alpha^3` imaginary component. -/
def alpha3Im : FExpr := quadMulIm alpha2Re alpha2Im alpha0 alpha1

/-- Shared accumulator real component on the visible stack. -/
def accRe : FExpr := s14
/-- Shared accumulator imaginary component on the visible stack. -/
def accIm : FExpr := s15
/-- Shared next-row accumulator real component. -/
def accReNext : FExpr := s14Next
/-- Shared next-row accumulator imaginary component. -/
def accImNext : FExpr := s15Next

/-- Shared `acc * alpha^2` real component. -/
def accAlpha2Re : FExpr := quadMulRe accRe accIm alpha2Re alpha2Im
/-- Shared `acc * alpha^2` imaginary component. -/
def accAlpha2Im : FExpr := quadMulIm accRe accIm alpha2Re alpha2Im

/-- Canonical selector for `CRYPTOSTREAM` opcode `110_0100` (`b6..b0`). -/
def isCryptostream : FExpr :=
  FExpr.times opBit6
    (FExpr.times opBit5
      (FExpr.times notOpBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for `HORNERBASE` opcode `101_1001` (`b6..b0`). -/
def isHornerbase : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 opBit0)))))

/-- Canonical selector for `HORNEREXT` opcode `101_1010` (`b6..b0`). -/
def isHornerext : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 notOpBit0)))))

-- CRYPTOSTREAM ----------------------------------------------------------------

/-- `CRYPTOSTREAM` constraints mirrored from Rust, in source order. -/
def cryptostreamConstraints : BaseConstraintSet := [
  transitionEq isCryptostream s8Next s8,
  transitionEq isCryptostream s9Next s9,
  transitionEq isCryptostream s10Next s10,
  transitionEq isCryptostream s11Next s11,
  transitionEq isCryptostream s12Next (FExpr.plus s12 eight),
  transitionEq isCryptostream s13Next (FExpr.plus s13 eight),
  transitionEq isCryptostream s14Next s14,
  transitionEq isCryptostream s15Next s15
]

-- HORNERBASE ------------------------------------------------------------------

/-- `HORNERBASE` tmp1 real helper (`decoder[USER_OP_HELPERS_OFFSET + 2]`). -/
def hornerbaseTmp1Re : FExpr := uopH2
/-- `HORNERBASE` tmp1 imaginary helper (`decoder[USER_OP_HELPERS_OFFSET + 3]`). -/
def hornerbaseTmp1Im : FExpr := uopH3
/-- `HORNERBASE` tmp0 real helper (`decoder[USER_OP_HELPERS_OFFSET + 4]`). -/
def hornerbaseTmp0Re : FExpr := uopH4
/-- `HORNERBASE` tmp0 imaginary helper (`decoder[USER_OP_HELPERS_OFFSET + 5]`). -/
def hornerbaseTmp0Im : FExpr := uopH5

/-- Expected `tmp0.re = (acc * alpha^2 + (c0 * alpha + c1)).re`. -/
def hornerbaseTmp0ExpectedRe : FExpr :=
  FExpr.plus accAlpha2Re (FExpr.plus (FExpr.times alpha0 s0) s1)

/-- Expected `tmp0.im = (acc * alpha^2 + (c0 * alpha + c1)).im`. -/
def hornerbaseTmp0ExpectedIm : FExpr :=
  FExpr.plus accAlpha2Im (FExpr.times alpha1 s0)

/-- Shared `tmp0 * alpha^3` real component. -/
def hornerbaseTmp0Alpha3Re : FExpr :=
  quadMulRe hornerbaseTmp0Re hornerbaseTmp0Im alpha3Re alpha3Im

/-- Shared `tmp0 * alpha^3` imaginary component. -/
def hornerbaseTmp0Alpha3Im : FExpr :=
  quadMulIm hornerbaseTmp0Re hornerbaseTmp0Im alpha3Re alpha3Im

/-- Expected `tmp1.re = (tmp0 * alpha^3 + (c2 * alpha^2 + c3 * alpha + c4)).re`. -/
def hornerbaseTmp1ExpectedRe : FExpr :=
  FExpr.plus hornerbaseTmp0Alpha3Re
    (FExpr.plus (FExpr.times alpha2Re s2)
      (FExpr.plus (FExpr.times alpha0 s3) s4))

/-- Expected `tmp1.im = (tmp0 * alpha^3 + (c2 * alpha^2 + c3 * alpha + c4)).im`. -/
def hornerbaseTmp1ExpectedIm : FExpr :=
  FExpr.plus hornerbaseTmp0Alpha3Im
    (FExpr.plus (FExpr.times alpha2Im s2) (FExpr.times alpha1 s3))

/-- Shared `tmp1 * alpha^3` real component. -/
def hornerbaseTmp1Alpha3Re : FExpr :=
  quadMulRe hornerbaseTmp1Re hornerbaseTmp1Im alpha3Re alpha3Im

/-- Shared `tmp1 * alpha^3` imaginary component. -/
def hornerbaseTmp1Alpha3Im : FExpr :=
  quadMulIm hornerbaseTmp1Re hornerbaseTmp1Im alpha3Re alpha3Im

/-- Expected `acc'.re = (tmp1 * alpha^3 + (c5 * alpha^2 + c6 * alpha + c7)).re`. -/
def hornerbaseAccExpectedRe : FExpr :=
  FExpr.plus hornerbaseTmp1Alpha3Re
    (FExpr.plus (FExpr.times alpha2Re s5)
      (FExpr.plus (FExpr.times alpha0 s6) s7))

/-- Expected `acc'.im = (tmp1 * alpha^3 + (c5 * alpha^2 + c6 * alpha + c7)).im`. -/
def hornerbaseAccExpectedIm : FExpr :=
  FExpr.plus hornerbaseTmp1Alpha3Im
    (FExpr.plus (FExpr.times alpha2Im s5) (FExpr.times alpha1 s6))

/-- `HORNERBASE` lower-stack stability constraints. -/
def hornerbaseUnchanged : BaseConstraintSet := [
  transitionEq isHornerbase s0Next s0,
  transitionEq isHornerbase s1Next s1,
  transitionEq isHornerbase s2Next s2,
  transitionEq isHornerbase s3Next s3,
  transitionEq isHornerbase s4Next s4,
  transitionEq isHornerbase s5Next s5,
  transitionEq isHornerbase s6Next s6,
  transitionEq isHornerbase s7Next s7,
  transitionEq isHornerbase s8Next s8,
  transitionEq isHornerbase s9Next s9,
  transitionEq isHornerbase s10Next s10,
  transitionEq isHornerbase s11Next s11,
  transitionEq isHornerbase s12Next s12,
  transitionEq isHornerbase s13Next s13
]

/-- `HORNERBASE` integrity constraints mirrored from Rust, in source order. -/
def hornerbaseIntegrity : BaseConstraintSet := [
  integrityEq isHornerbase hornerbaseTmp0Re hornerbaseTmp0ExpectedRe,
  integrityEq isHornerbase hornerbaseTmp0Im hornerbaseTmp0ExpectedIm,
  integrityEq isHornerbase hornerbaseTmp1Re hornerbaseTmp1ExpectedRe,
  integrityEq isHornerbase hornerbaseTmp1Im hornerbaseTmp1ExpectedIm
]

/-- `HORNERBASE` transition constraints mirrored from Rust, in source order. -/
def hornerbaseTransition : BaseConstraintSet := [
  transitionEq isHornerbase accReNext hornerbaseAccExpectedRe,
  transitionEq isHornerbase accImNext hornerbaseAccExpectedIm
]

/-- Full `HORNERBASE` constraint block. -/
def hornerbaseConstraints : BaseConstraintSet :=
  hornerbaseUnchanged ++ hornerbaseIntegrity ++ hornerbaseTransition

-- HORNEREXT -------------------------------------------------------------------

/-- `HORNEREXT` tmp real helper (`decoder[USER_OP_HELPERS_OFFSET + 4]`). -/
def hornerextTmpRe : FExpr := uopH4
/-- `HORNEREXT` tmp imaginary helper (`decoder[USER_OP_HELPERS_OFFSET + 5]`). -/
def hornerextTmpIm : FExpr := uopH5

/-- Expected `tmp.re = (acc * alpha^2 + (c0 * alpha + c1)).re`. -/
def hornerextTmpExpectedRe : FExpr :=
  FExpr.plus accAlpha2Re
    (FExpr.plus (quadMulRe alpha0 alpha1 s0 s1) s2)

/-- Expected `tmp.im = (acc * alpha^2 + (c0 * alpha + c1)).im`. -/
def hornerextTmpExpectedIm : FExpr :=
  FExpr.plus accAlpha2Im
    (FExpr.plus (quadMulIm alpha0 alpha1 s0 s1) s3)

/-- Shared `tmp * alpha^2` real component. -/
def hornerextTmpAlpha2Re : FExpr :=
  quadMulRe hornerextTmpRe hornerextTmpIm alpha2Re alpha2Im

/-- Shared `tmp * alpha^2` imaginary component. -/
def hornerextTmpAlpha2Im : FExpr :=
  quadMulIm hornerextTmpRe hornerextTmpIm alpha2Re alpha2Im

/-- Expected `acc'.re = (tmp * alpha^2 + (c2 * alpha + c3)).re`. -/
def hornerextAccExpectedRe : FExpr :=
  FExpr.plus hornerextTmpAlpha2Re
    (FExpr.plus (quadMulRe alpha0 alpha1 s4 s5) s6)

/-- Expected `acc'.im = (tmp * alpha^2 + (c2 * alpha + c3)).im`. -/
def hornerextAccExpectedIm : FExpr :=
  FExpr.plus hornerextTmpAlpha2Im
    (FExpr.plus (quadMulIm alpha0 alpha1 s4 s5) s7)

/-- `HORNEREXT` lower-stack stability constraints. -/
def hornerextUnchanged : BaseConstraintSet := [
  transitionEq isHornerext s0Next s0,
  transitionEq isHornerext s1Next s1,
  transitionEq isHornerext s2Next s2,
  transitionEq isHornerext s3Next s3,
  transitionEq isHornerext s4Next s4,
  transitionEq isHornerext s5Next s5,
  transitionEq isHornerext s6Next s6,
  transitionEq isHornerext s7Next s7,
  transitionEq isHornerext s8Next s8,
  transitionEq isHornerext s9Next s9,
  transitionEq isHornerext s10Next s10,
  transitionEq isHornerext s11Next s11,
  transitionEq isHornerext s12Next s12,
  transitionEq isHornerext s13Next s13
]

/-- `HORNEREXT` integrity constraints mirrored from Rust, in source order. -/
def hornerextIntegrity : BaseConstraintSet := [
  integrityEq isHornerext hornerextTmpRe hornerextTmpExpectedRe,
  integrityEq isHornerext hornerextTmpIm hornerextTmpExpectedIm
]

/-- `HORNEREXT` transition constraints mirrored from Rust, in source order. -/
def hornerextTransition : BaseConstraintSet := [
  transitionEq isHornerext accReNext hornerextAccExpectedRe,
  transitionEq isHornerext accImNext hornerextAccExpectedIm
]

/-- Full `HORNEREXT` constraint block. -/
def hornerextConstraints : BaseConstraintSet :=
  hornerextUnchanged ++ hornerextIntegrity ++ hornerextTransition

/-- Number of stack-crypto constraints mirrored from Rust. -/
def numConstraints : Nat := 46

/-- Full stack-crypto base-constraint slice in Rust source order. -/
def base : BaseConstraintSet := allOf <|
  cryptostreamConstraints ++ hornerbaseConstraints ++ hornerextConstraints

section SmokeTests

-- No `MLOADW` smoke test belongs here: the referenced Rust stack-crypto module
-- contains only `CRYPTOSTREAM`, `HORNERBASE`, and `HORNEREXT`.

#eval base.length == numConstraints

private def cryptostreamCurr (j : MainCol) : Felt :=
  match j.val with
  | 9 => 1
  | 12 => 1
  | 13 => 1
  | 38 => 10
  | 39 => 11
  | 40 => 12
  | 41 => 13
  | 42 => 20
  | 43 => 21
  | 44 => 30
  | 45 => 31
  | _ => 0

private def goodCryptostreamNext (j : MainCol) : Felt :=
  match j.val with
  | 38 => 10
  | 39 => 11
  | 40 => 12
  | 41 => 13
  | 42 => 28
  | 43 => 29
  | 44 => 30
  | 45 => 31
  | _ => 0

private def badCryptostreamNext (j : MainCol) : Felt :=
  match j.val with
  | 38 => 10
  | 39 => 11
  | 40 => 12
  | 41 => 13
  | 42 => 27
  | 43 => 29
  | 44 => 30
  | 45 => 31
  | _ => 0

private def goodCryptostreamRow : AirRow := {
  curr := cryptostreamCurr
  next := goodCryptostreamNext
  isTransition := 1
}

private def badCryptostreamRow : AirRow := {
  curr := cryptostreamCurr
  next := badCryptostreamNext
  isTransition := 1
}

private def hornerbaseZeroCurr (j : MainCol) : Felt :=
  match j.val with
  | 7 => 1
  | 10 => 1
  | 11 => 1
  | 13 => 1
  | _ => 0

private def badHornerbaseZeroNext (j : MainCol) : Felt :=
  match j.val with
  | 44 => 1
  | _ => 0

private def goodHornerbaseZeroRow : AirRow := {
  curr := hornerbaseZeroCurr
  next := fun _ => 0
  isTransition := 1
}

private def badHornerbaseZeroRow : AirRow := {
  curr := hornerbaseZeroCurr
  next := badHornerbaseZeroNext
  isTransition := 1
}

private def hornerextZeroCurr (j : MainCol) : Felt :=
  match j.val with
  | 8 => 1
  | 10 => 1
  | 11 => 1
  | 13 => 1
  | _ => 0

private def badHornerextZeroCurr (j : MainCol) : Felt :=
  match j.val with
  | 8 => 1
  | 10 => 1
  | 11 => 1
  | 13 => 1
  | 20 => 1
  | _ => 0

private def goodHornerextZeroRow : AirRow := {
  curr := hornerextZeroCurr
  next := fun _ => 0
  isTransition := 1
}

private def badHornerextZeroRow : AirRow := {
  curr := badHornerextZeroCurr
  next := fun _ => 0
  isTransition := 1
}

#eval checkBase goodCryptostreamRow base
#eval checkBase badCryptostreamRow base
#eval checkBase goodHornerbaseZeroRow base
#eval checkBase badHornerbaseZeroRow base
#eval checkBase goodHornerextZeroRow base
#eval checkBase badHornerextZeroRow base

end SmokeTests

end MidenLean.AIR.Semantics.Subsystems.StackCrypto
