import MidenLean.AIR.Semantics.Subsystems.ChipletSelectors
/-!
# ACE Chiplet AIR Implementation Layer

This file encodes the canonical ACE-chiplet main-trace AIR slice backed by
`air/src/constraints/chiplets/ace.rs`.

The shared chiplet trace begins at `CHIPLETS_OFFSET = 51`. ACE only uses the
shared selectors `s0 .. s3` at `cols 51 .. 54`, so the ACE base-constraint
payload touched by `ace.rs` begins at `col 55`. ACE is active when `s0 = 1`,
`s1 = 1`, `s2 = 1`, and `s3 = 0`. The resulting ACE-local layout is:

- shared selectors used by ACE: `s0 = col 51`, `s1 = col 52`, `s2 = col 53`,
  `s3 = col 54`
- `sstart = col 55`
- `sblock = col 56`
- `ctx = col 57`
- `ptr = col 58`
- `clk = col 59`
- `op = col 60`
- `id0 = col 61`
- `v0_0 = col 62`
- `v0_1 = col 63`
- `id1 = col 64`
- `v1_0 = col 65`
- `v1_1 = col 66`
- `n_eval / id2 = col 67`
- `v2_0 = col 68`
- `v2_1 / m1 = col 69`

Rust also has an `m0` column used by the separate ACE wiring-bus constraint.
Under the ACE-local four-selector offset used here, that bus-only column is
outside this base-constraint transcription.

Rust enforces exactly 20 base constraints in this order:

1. `sstart` and `sblock` are binary on ACE rows.
2. Section flags enforce start/read/end discipline.
3. Within a section, `ctx` and `clk` stay constant, `ptr` advances by `+4` on
   READ rows or `+1` on EVAL rows, and `id0` decrements by `2` or `1`.
4. READ rows require `id1 = id0 - 1`.
5. READ-to-EVAL handoff tracks the stored `n_eval`.
6. EVAL rows require `op ∈ {-1, 0, 1}`.
7. EVAL rows enforce either quadratic-extension multiplication or the
   `v1 + op * v2` linear form, depending on `op²`.
8. Section-final rows force `v0 = 0` and `id0 = 0`.
9. The first ACE row entered from memory has `sstart' = 1`.
-/

namespace MidenLean.AIR.Semantics.Subsystems.ChipletAce

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder
open MidenLean.AIR.Semantics.Check

/-- Shared chiplet trace offset `CHIPLETS_OFFSET = 51`. -/
abbrev chipletsOffset : Nat :=
  MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.chipletsOffset

/-- First ACE payload column after the ACE-relevant selectors `s0 .. s3` (`col 55`). -/
abbrev aceTraceOffset : Nat := chipletsOffset + 4

/-- Current-row shared selector `s0`. -/
abbrev s0 : FExpr := MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.s0

/-- Current-row shared selector `s1`. -/
abbrev s1 : FExpr := MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.s1

/-- Current-row shared selector `s2`. -/
abbrev s2 : FExpr := MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.s2

/-- Next-row shared selector `s2'`. -/
abbrev s2Next : FExpr := MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.s2Next

/-- Next-row shared selector `s3'`. -/
abbrev s3Next : FExpr := MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.s3Next

/-- Current-row `sstart` column (`col 55`). -/
def sstartCol : MainCol := ⟨aceTraceOffset, by decide⟩

/-- Current-row `sblock` column (`col 56`). -/
def sblockCol : MainCol := ⟨aceTraceOffset + 1, by decide⟩

/-- Current-row `ctx` column (`col 57`). -/
def ctxCol : MainCol := ⟨aceTraceOffset + 2, by decide⟩

/-- Current-row `ptr` column (`col 58`). -/
def ptrCol : MainCol := ⟨aceTraceOffset + 3, by decide⟩

/-- Current-row `clk` column (`col 59`). -/
def clkCol : MainCol := ⟨aceTraceOffset + 4, by decide⟩

/-- Current-row `op` column (`col 60`). -/
def opCol : MainCol := ⟨aceTraceOffset + 5, by decide⟩

/-- Current-row `id0` column (`col 61`). -/
def id0Col : MainCol := ⟨aceTraceOffset + 6, by decide⟩

/-- Current-row `v0_0` column (`col 62`). -/
def v00Col : MainCol := ⟨aceTraceOffset + 7, by decide⟩

/-- Current-row `v0_1` column (`col 63`). -/
def v01Col : MainCol := ⟨aceTraceOffset + 8, by decide⟩

/-- Current-row `id1` column (`col 64`). -/
def id1Col : MainCol := ⟨aceTraceOffset + 9, by decide⟩

/-- Current-row `v1_0` column (`col 65`). -/
def v10Col : MainCol := ⟨aceTraceOffset + 10, by decide⟩

/-- Current-row `v1_1` column (`col 66`). -/
def v11Col : MainCol := ⟨aceTraceOffset + 11, by decide⟩

/-- Current-row `n_eval / id2` column (`col 67`). -/
def nEvalCol : MainCol := ⟨aceTraceOffset + 12, by decide⟩

/-- Current-row `v2_0` column (`col 68`). -/
def v20Col : MainCol := ⟨aceTraceOffset + 13, by decide⟩

/-- Current-row `v2_1 / m1` column (`col 69`). -/
def v21Col : MainCol := ⟨aceTraceOffset + 14, by decide⟩

/-- Current-row ACE-active flag `s0 * s1 * s2 * (1 - s3)`. -/
abbrev aceFlag : FExpr :=
  MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.aceChipletFlag

/-- Current-row memory-active flag `s0 * s1 * (1 - s2)`. -/
abbrev memoryFlag : FExpr :=
  MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.memoryChipletFlag

/-- Current-row `sstart`. -/
def sstart : FExpr := FExpr.curr sstartCol

/-- Next-row `sstart'`. -/
def sstartNext : FExpr := FExpr.next sstartCol

/-- Current-row `sblock`. -/
def sblock : FExpr := FExpr.curr sblockCol

/-- Next-row `sblock'`. -/
def sblockNext : FExpr := FExpr.next sblockCol

/-- Current-row `ctx`. -/
def ctx : FExpr := FExpr.curr ctxCol

/-- Next-row `ctx'`. -/
def ctxNext : FExpr := FExpr.next ctxCol

/-- Current-row `ptr`. -/
def ptr : FExpr := FExpr.curr ptrCol

/-- Next-row `ptr'`. -/
def ptrNext : FExpr := FExpr.next ptrCol

/-- Current-row `clk`. -/
def clk : FExpr := FExpr.curr clkCol

/-- Next-row `clk'`. -/
def clkNext : FExpr := FExpr.next clkCol

/-- Current-row `op`. -/
def op : FExpr := FExpr.curr opCol

/-- Current-row `id0`. -/
def id0 : FExpr := FExpr.curr id0Col

/-- Next-row `id0'`. -/
def id0Next : FExpr := FExpr.next id0Col

/-- Current-row `v0_0`. -/
def v00 : FExpr := FExpr.curr v00Col

/-- Current-row `v0_1`. -/
def v01 : FExpr := FExpr.curr v01Col

/-- Current-row `id1`. -/
def id1 : FExpr := FExpr.curr id1Col

/-- Current-row `v1_0`. -/
def v10 : FExpr := FExpr.curr v10Col

/-- Current-row `v1_1`. -/
def v11 : FExpr := FExpr.curr v11Col

/-- Current-row `n_eval`. -/
def nEval : FExpr := FExpr.curr nEvalCol

/-- Next-row `n_eval'`. -/
def nEvalNext : FExpr := FExpr.next nEvalCol

/-- Current-row `v2_0`. -/
def v20 : FExpr := FExpr.curr v20Col

/-- Current-row `v2_1`. -/
def v21 : FExpr := FExpr.curr v21Col

/-- Constant `1`. -/
def one : FExpr := FExpr.const 1

/-- Constant `4`. -/
def four : FExpr := FExpr.const 4

/-- Constant `7`, the quadratic-extension residue. -/
def seven : FExpr := FExpr.const 7

/-- Canonical complement expression `1 - expr`. -/
def oneMinus (expr : FExpr) : FExpr := FExpr.minus one expr

/-- Double an AIR expression. -/
def double (expr : FExpr) : FExpr := FExpr.plus expr expr

/-- Binary OR helper `a + b - a * b`. -/
def binaryOr (a b : FExpr) : FExpr :=
  FExpr.minus (FExpr.plus a b) (FExpr.times a b)

/-- Canonical integrity-gated zero constraint. -/
def integrityZero (selector expr : FExpr) : BaseConstraint :=
  gate selector <| assertZero expr

/-- Canonical integrity-gated equality constraint. -/
def integrityEq (selector lhs rhs : FExpr) : BaseConstraint :=
  gate selector <| assertEq lhs rhs

/-- Canonical transition-gated zero constraint. -/
def transitionZero (selector expr : FExpr) : BaseConstraint :=
  whenTransition <| gate selector <| assertZero expr

/-- Canonical transition-gated equality constraint. -/
def transitionEq (selector lhs rhs : FExpr) : BaseConstraint :=
  whenTransition <| gate selector <| assertEq lhs rhs

/-- Selector for ACE rows whose successor still lies in ACE. -/
def flagAceNext : FExpr := oneMinus s3Next

/-- Selector for the last ACE row before exiting to kernel ROM. -/
def flagAceLast : FExpr := s3Next

/-- Selector for successors that remain inside the current ACE section. -/
def flagWithinSection : FExpr := oneMinus sstartNext

/-- Selector for the first ACE row entered from memory. -/
def flagNextRowFirstAce : FExpr :=
  FExpr.times (FExpr.times memoryFlag s2Next) (oneMinus s3Next)

/-- READ-block flag `1 - sblock`. -/
def fRead : FExpr := oneMinus sblock

/-- EVAL-block flag `sblock`. -/
def fEval : FExpr := sblock

/-- Next-row READ-block flag `1 - sblock'`. -/
def fReadNext : FExpr := oneMinus sblockNext

/-- Next-row EVAL-block flag `sblock'`. -/
def fEvalNext : FExpr := sblockNext

/-- Next-row "not a section start" flag `1 - sstart'`. -/
def fNext : FExpr := oneMinus sstartNext

/-- Section-end flag
`OR((1 - s3') * sstart', s3')`. -/
def fEnd : FExpr :=
  binaryOr (FExpr.times flagAceNext sstartNext) s3Next

/-- Shared gate for transitions that stay inside the current ACE section. -/
def withinSectionGate : FExpr :=
  FExpr.times (FExpr.times aceFlag flagAceNext) flagWithinSection

/-- Expected in-section pointer update `ptr + 4 * f_read + f_eval`. -/
def expectedPtrNext : FExpr :=
  FExpr.plus ptr <| FExpr.plus (FExpr.times four fRead) fEval

/-- Expected in-section `id0` update `id0' + 2 * f_read + f_eval`. -/
def expectedId0 : FExpr :=
  FExpr.plus id0Next <| FExpr.plus (double fRead) fEval

/-- READ-to-EVAL selection term
`f_read' * n_eval' + f_eval' * id0'`. -/
def readToEvalSelected : FExpr :=
  FExpr.plus (FExpr.times fReadNext nEvalNext) (FExpr.times fEvalNext id0Next)

/-- Real part of quadratic-extension multiplication with `u² = 7`. -/
def quadMulRe (a0 a1 b0 b1 : FExpr) : FExpr :=
  FExpr.plus (FExpr.times a0 b0) (FExpr.times seven (FExpr.times a1 b1))

/-- Imaginary part of quadratic-extension multiplication with `u² = 7`. -/
def quadMulIm (a0 a1 b0 b1 : FExpr) : FExpr :=
  FExpr.plus (FExpr.times a0 b1) (FExpr.times a1 b0)

/-- Linear real part `v1_0 + op * v2_0`. -/
def linearExpected0 : FExpr := FExpr.plus v10 (FExpr.times op v20)

/-- Linear imaginary part `v1_1 + op * v2_1`. -/
def linearExpected1 : FExpr := FExpr.plus v11 (FExpr.times op v21)

/-- Nonlinear real part `v1 * v2`. -/
def nonlinearExpected0 : FExpr := quadMulRe v10 v11 v20 v21

/-- Nonlinear imaginary part `v1 * v2`. -/
def nonlinearExpected1 : FExpr := quadMulIm v10 v11 v20 v21

/-- Selector `op²`, which chooses linear mode for `op = ±1` and nonlinear mode
for `op = 0`. -/
def opSquare : FExpr := FExpr.times op op

/-- Expected EVAL result real component. -/
def expectedEval0 : FExpr :=
  FExpr.plus
    (FExpr.times opSquare (FExpr.minus linearExpected0 nonlinearExpected0))
    nonlinearExpected0

/-- Expected EVAL result imaginary component. -/
def expectedEval1 : FExpr :=
  FExpr.plus
    (FExpr.times opSquare (FExpr.minus linearExpected1 nonlinearExpected1))
    nonlinearExpected1

/-- Canonical AIR binary constraint for `sstart`. -/
def sstartBinary : BaseConstraint :=
  integrityZero aceFlag <| FExpr.times sstart (FExpr.minus sstart one)

/-- Canonical AIR binary constraint for `sblock`. -/
def sblockBinary : BaseConstraint :=
  integrityZero aceFlag <| FExpr.times sblock (FExpr.minus sblock one)

/-- Canonical AIR constraint: the last ACE row cannot be a section start. -/
def lastAceRowNotSectionStart : BaseConstraint :=
  transitionZero (FExpr.times aceFlag flagAceLast) sstart

/-- Canonical AIR constraint: ACE cannot contain consecutive section starts. -/
def noConsecutiveSectionStarts : BaseConstraint :=
  transitionZero (FExpr.times aceFlag flagAceNext) <| FExpr.times sstart sstartNext

/-- Canonical AIR constraint: every section starts with a READ block. -/
def sectionStartsWithRead : BaseConstraint :=
  integrityZero (FExpr.times aceFlag sstart) sblock

/-- Canonical AIR constraint: an EVAL block cannot be followed by a READ block
within the same section. -/
def noEvalToReadWithinSection : BaseConstraint :=
  transitionZero
    (FExpr.times (FExpr.times (FExpr.times aceFlag flagAceNext) fNext) sblock)
    (oneMinus sblockNext)

/-- Canonical AIR constraint: every section ends with an EVAL block. -/
def sectionsEndWithEval : BaseConstraint :=
  transitionZero (FExpr.times aceFlag fEnd) (oneMinus sblock)

/-- Canonical AIR within-section context-stability constraint. -/
def ctxConsistencyWithinSection : BaseConstraint :=
  transitionZero withinSectionGate (FExpr.minus ctxNext ctx)

/-- Canonical AIR within-section clock-stability constraint. -/
def clkConsistencyWithinSection : BaseConstraint :=
  transitionZero withinSectionGate (FExpr.minus clkNext clk)

/-- Canonical AIR within-section pointer-update constraint. -/
def ptrAdvanceWithinSection : BaseConstraint :=
  transitionEq withinSectionGate ptrNext expectedPtrNext

/-- Canonical AIR within-section `id0`-update constraint. -/
def id0DecrementsWithinSection : BaseConstraint :=
  transitionEq withinSectionGate id0 expectedId0

/-- Canonical AIR READ-block wire-ID constraint `id1 = id0 - 1`. -/
def readIdsConsecutive : BaseConstraint :=
  integrityZero (FExpr.times aceFlag fRead) <|
    FExpr.plus (FExpr.minus id1 id0) one

/-- Canonical AIR READ-to-EVAL handoff constraint. -/
def readToEvalHandoff : BaseConstraint :=
  transitionZero (FExpr.times aceFlag fRead) <|
    FExpr.minus readToEvalSelected nEval

/-- Canonical AIR EVAL-op range constraint `op * (op - 1) * (op + 1) = 0`. -/
def evalOpRange : BaseConstraint :=
  integrityZero (FExpr.times aceFlag fEval) <|
    FExpr.times (FExpr.times op (FExpr.minus op one)) (FExpr.plus op one)

/-- Canonical AIR EVAL-result real-component constraint. -/
def evalResult0 : BaseConstraint :=
  integrityEq (FExpr.times aceFlag fEval) expectedEval0 v00

/-- Canonical AIR EVAL-result imaginary-component constraint. -/
def evalResult1 : BaseConstraint :=
  integrityEq (FExpr.times aceFlag fEval) expectedEval1 v01

/-- Canonical AIR finalization constraint `v0_0 = 0`. -/
def finalV00Zero : BaseConstraint :=
  transitionZero (FExpr.times aceFlag fEnd) v00

/-- Canonical AIR finalization constraint `v0_1 = 0`. -/
def finalV01Zero : BaseConstraint :=
  transitionZero (FExpr.times aceFlag fEnd) v01

/-- Canonical AIR finalization constraint `id0 = 0`. -/
def finalId0Zero : BaseConstraint :=
  transitionZero (FExpr.times aceFlag fEnd) id0

/-- Canonical AIR first-row constraint `sstart' = 1` when entering ACE from
memory. -/
def firstRowStart : BaseConstraint :=
  transitionEq flagNextRowFirstAce sstartNext one

/-- Binary constraints in Rust assertion order. -/
def binaryConstraints : BaseConstraintSet :=
  [sstartBinary, sblockBinary]

/-- Section-flag constraints in Rust assertion order. -/
def sectionFlagConstraints : BaseConstraintSet :=
  [lastAceRowNotSectionStart, noConsecutiveSectionStarts,
   sectionStartsWithRead, noEvalToReadWithinSection, sectionsEndWithEval]

/-- Within-section transition constraints in Rust assertion order. -/
def withinSectionConstraints : BaseConstraintSet :=
  [ctxConsistencyWithinSection, clkConsistencyWithinSection,
   ptrAdvanceWithinSection, id0DecrementsWithinSection]

/-- EVAL-result constraints in Rust assertion order. -/
def evalResultConstraints : BaseConstraintSet :=
  [evalResult0, evalResult1]

/-- Finalization constraints in Rust assertion order. -/
def finalizationConstraints : BaseConstraintSet :=
  [finalV00Zero, finalV01Zero, finalId0Zero]

/-- Canonical ACE-chiplet base constraints in Rust assertion order. -/
def base : BaseConstraintSet := allOf <|
  binaryConstraints ++
  sectionFlagConstraints ++
  withinSectionConstraints ++
  [readIdsConsecutive, readToEvalHandoff, evalOpRange] ++
  evalResultConstraints ++
  finalizationConstraints ++
  [firstRowStart]

private def aceCols
    (s0Val s1Val s2Val s3Val s4Val
     sstartVal sblockVal ctxVal ptrVal clkVal opVal id0Val v00Val v01Val
     id1Val v10Val v11Val nEvalVal v20Val v21Val : Felt)
    (j : MainCol) : Felt :=
  match j.val with
  | 51 => s0Val
  | 52 => s1Val
  | 53 => s2Val
  | 54 => s3Val
  | 55 => s4Val
  | 56 => sstartVal
  | 57 => sblockVal
  | 58 => ctxVal
  | 59 => ptrVal
  | 60 => clkVal
  | 61 => opVal
  | 62 => id0Val
  | 63 => v00Val
  | 64 => v01Val
  | 65 => id1Val
  | 66 => v10Val
  | 67 => v11Val
  | 68 => nEvalVal
  | 69 => v20Val
  | 70 => v21Val
  | _ => 0

private def memoryStub : MainCol → Felt :=
  aceCols 1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0

private def kernelRomStub : MainCol → Felt :=
  aceCols 1 1 1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0

private def goodEntryRow : AirRow := {
  curr := memoryStub
  next := aceCols 1 1 1 0 0 1 0 5 100 9 0 4 0 0 3 0 0 2 0 0
  isTransition := 1
}

private def badEntryRow : AirRow := {
  curr := memoryStub
  next := aceCols 1 1 1 0 0 0 0 5 100 9 0 4 0 0 3 0 0 2 0 0
  isTransition := 1
}

private def goodReadRow : AirRow := {
  curr := aceCols 1 1 1 0 0 1 0 5 100 9 0 4 0 0 3 0 0 2 0 0
  next := aceCols 1 1 1 0 0 0 0 5 104 9 0 2 0 0 1 0 0 2 0 0
  isTransition := 1
}

private def badReadRow : AirRow := {
  curr := aceCols 1 1 1 0 0 1 0 5 100 9 0 4 0 0 3 0 0 2 0 0
  next := aceCols 1 1 1 0 0 0 0 5 105 9 0 2 0 0 1 0 0 2 0 0
  isTransition := 1
}

private def goodEvalRow : AirRow := {
  curr := aceCols 1 1 1 0 0 0 1 5 104 9 0 3 157 29 2 2 3 0 5 7
  next := aceCols 1 1 1 0 0 0 1 5 105 9 0 2 0 0 0 0 0 0 0 0
  isTransition := 1
}

private def badEvalRow : AirRow := {
  curr := aceCols 1 1 1 0 0 0 1 5 104 9 0 3 157 30 2 2 3 0 5 7
  next := aceCols 1 1 1 0 0 0 1 5 105 9 0 2 0 0 0 0 0 0 0 0
  isTransition := 1
}

private def goodFinalRow : AirRow := {
  curr := aceCols 1 1 1 0 0 0 1 5 105 9 1 0 0 0 0 0 0 0 0 0
  next := kernelRomStub
  isTransition := 1
}

private def badFinalRow : AirRow := {
  curr := aceCols 1 1 1 0 0 0 1 5 105 9 1 1 0 0 0 0 0 0 0 0
  next := kernelRomStub
  isTransition := 1
}

#eval checkBase goodEntryRow base
#eval checkBase badEntryRow base
#eval checkBase goodReadRow base
#eval checkBase badReadRow base
#eval checkBase goodEvalRow base
#eval checkBase badEvalRow base
#eval checkBase goodFinalRow base
#eval checkBase badFinalRow base

end MidenLean.AIR.Semantics.Subsystems.ChipletAce
