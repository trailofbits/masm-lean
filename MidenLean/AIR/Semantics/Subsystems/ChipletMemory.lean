import MidenLean.AIR.Semantics.Subsystems.ChipletSelectors
/-!
# Memory Chiplet AIR Implementation Layer

This file encodes the canonical memory-chiplet main-trace AIR slice backed by
`air/src/constraints/chiplets/memory.rs`.

The shared chiplet trace begins at `CHIPLETS_OFFSET = 51`. The memory chiplet
is active when the selector prefix satisfies `s0 = 1`, `s1 = 1`, and `s2 = 0`,
so Rust addresses its local trace with
`MEMORY_TRACE_OFFSET = CHIPLETS_OFFSET + 3 = 54`. This means the memory payload
reuses global `col 54` and `col 55`, which later chiplets interpret as `s3` and
`s4`. The resulting layout is:

- shared selectors: `s0 = col 51`, `s1 = col 52`, `s2 = col 53`
- `is_read = col 54`
- `is_word = col 55`
- `ctx = col 56`
- `word_addr = col 57`
- `idx0 = col 58`
- `idx1 = col 59`
- `clk = col 60`
- `v[0..3] = cols 61..64`
- `d0 = col 65`
- `d1 = col 66`
- `d_inv = col 67`
- `f_scw = col 68`

Rust enforces exactly 21 base constraints in this order:

1. `is_read`, `is_word`, `idx0`, and `idx1` are binary on active memory rows.
2. Word accesses force `idx0 = idx1 = 0`.
3. On the first memory row entered from bitwise, unwritten value lanes are zero.
4. On memory-to-memory transitions, `n0 = (ctx' - ctx) * d_inv'` and
   `n1 = (word_addr' - word_addr) * d_inv'` behave as binary branch flags.
5. The selected monotone delta is decomposed as `d1' * 2^16 + d0'`.
6. The next-row same-context/word flag is `f_scw' = (1 - n0) * (1 - n1)`.
7. If context, word, and clock are all unchanged, both accesses must be reads.
8. Value lanes not written on the next row either persist (`f_scw' = 1`) or
   reset to zero (`f_scw' = 0`).
-/

namespace MidenLean.AIR.Semantics.Subsystems.ChipletMemory

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder
open MidenLean.AIR.Semantics.Check

/-- Shared chiplet trace offset `CHIPLETS_OFFSET = 51`. -/
abbrev chipletsOffset : Nat :=
  MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.chipletsOffset

/-- Rust `MEMORY_TRACE_OFFSET = CHIPLETS_OFFSET + 3 = 54`. -/
abbrev memoryTraceOffset : Nat := chipletsOffset + 3

/-- First memory value column (`col 61`). -/
abbrev memoryValueOffset : Nat := memoryTraceOffset + 7

/-- Typed memory-lane index `0..3`. -/
abbrev ValueIndex := Fin 4

/-- Current-row shared selector `s0`. -/
abbrev s0 : FExpr := MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.s0

/-- Current-row shared selector `s1`. -/
abbrev s1 : FExpr := MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.s1

/-- Current-row shared selector `s2`. -/
abbrev s2 : FExpr := MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.s2

/-- Next-row shared selector `s1'`. -/
abbrev s1Next : FExpr := MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.s1Next

/-- Next-row shared selector `s2'`. -/
abbrev s2Next : FExpr := MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.s2Next

/-- Current-row `is_read` column (`col 54`). -/
def isReadCol : MainCol := ⟨memoryTraceOffset, by decide⟩

/-- Current-row `is_word` column (`col 55`). -/
def isWordCol : MainCol := ⟨memoryTraceOffset + 1, by decide⟩

/-- Current-row `ctx` column (`col 56`). -/
def ctxCol : MainCol := ⟨memoryTraceOffset + 2, by decide⟩

/-- Current-row `word_addr` column (`col 57`). -/
def wordAddrCol : MainCol := ⟨memoryTraceOffset + 3, by decide⟩

/-- Current-row `idx0` column (`col 58`). -/
def idx0Col : MainCol := ⟨memoryTraceOffset + 4, by decide⟩

/-- Current-row `idx1` column (`col 59`). -/
def idx1Col : MainCol := ⟨memoryTraceOffset + 5, by decide⟩

/-- Current-row `clk` column (`col 60`). -/
def clkCol : MainCol := ⟨memoryTraceOffset + 6, by decide⟩

/-- Current-row `v[i]` value lane (`cols 61..64`). -/
def valueCol (i : ValueIndex) : MainCol := ⟨memoryValueOffset + i.val, by
  have hlt : memoryValueOffset + i.val < memoryValueOffset + 4 :=
    Nat.add_lt_add_left i.is_lt memoryValueOffset
  exact lt_of_lt_of_le hlt (by decide)
⟩

/-- Current-row `d0` column (`col 65`). -/
def d0Col : MainCol := ⟨memoryTraceOffset + 11, by decide⟩

/-- Current-row `d1` column (`col 66`). -/
def d1Col : MainCol := ⟨memoryTraceOffset + 12, by decide⟩

/-- Current-row `d_inv` column (`col 67`). -/
def dInvCol : MainCol := ⟨memoryTraceOffset + 13, by decide⟩

/-- Current-row `f_scw` column (`col 68`). -/
def sameCtxWordFlagCol : MainCol := ⟨memoryTraceOffset + 14, by decide⟩

/-- Current-row chiplet-active flag `s0 * s1 * (1 - s2)`. -/
abbrev memoryFlag : FExpr :=
  MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.memoryChipletFlag

/-- Current-row `is_read`. -/
def isRead : FExpr := FExpr.curr isReadCol

/-- Next-row `is_read'`. -/
def isReadNext : FExpr := FExpr.next isReadCol

/-- Current-row `is_word`. -/
def isWord : FExpr := FExpr.curr isWordCol

/-- Next-row `is_word'`. -/
def isWordNext : FExpr := FExpr.next isWordCol

/-- Current-row `ctx`. -/
def ctx : FExpr := FExpr.curr ctxCol

/-- Next-row `ctx'`. -/
def ctxNext : FExpr := FExpr.next ctxCol

/-- Current-row `word_addr`. -/
def wordAddr : FExpr := FExpr.curr wordAddrCol

/-- Next-row `word_addr'`. -/
def wordAddrNext : FExpr := FExpr.next wordAddrCol

/-- Current-row `idx0`. -/
def idx0 : FExpr := FExpr.curr idx0Col

/-- Next-row `idx0'`. -/
def idx0Next : FExpr := FExpr.next idx0Col

/-- Current-row `idx1`. -/
def idx1 : FExpr := FExpr.curr idx1Col

/-- Next-row `idx1'`. -/
def idx1Next : FExpr := FExpr.next idx1Col

/-- Current-row `clk`. -/
def clk : FExpr := FExpr.curr clkCol

/-- Next-row `clk'`. -/
def clkNext : FExpr := FExpr.next clkCol

/-- Current-row `v[i]`. -/
def value (i : ValueIndex) : FExpr := FExpr.curr (valueCol i)

/-- Next-row `v'[i]`. -/
def valueNext (i : ValueIndex) : FExpr := FExpr.next (valueCol i)

/-- Next-row `d0'`. -/
def d0Next : FExpr := FExpr.next d0Col

/-- Next-row `d1'`. -/
def d1Next : FExpr := FExpr.next d1Col

/-- Next-row `d_inv'`. -/
def dInvNext : FExpr := FExpr.next dInvCol

/-- Current-row `f_scw`. -/
def sameCtxWordFlag : FExpr := FExpr.curr sameCtxWordFlagCol

/-- Next-row `f_scw'`. -/
def sameCtxWordFlagNext : FExpr := FExpr.next sameCtxWordFlagCol

/-- Constant `1`. -/
def one : FExpr := FExpr.const 1

/-- Constant `2^16`. -/
def twoPow16 : FExpr := FExpr.const 65536

/-- Canonical complement expression `1 - expr`. -/
def oneMinus (expr : FExpr) : FExpr := FExpr.minus one expr

/-- Selector for transitions that remain inside the memory chiplet:
`s0 * s1 * (1 - s2')`. -/
def flagMemoryActiveNotLast : FExpr :=
  FExpr.times (FExpr.times s0 s1) (oneMinus s2Next)

/-- Selector for transitions from bitwise into the first memory row:
`(1 - s1) * s0 * s1' * (1 - s2')`. -/
def flagNextRowFirstMemory : FExpr :=
  FExpr.times
    (FExpr.times (FExpr.times (oneMinus s1) s0) s1Next)
    (oneMinus s2Next)

/-- Canonical integrity-gated zero constraint. -/
def integrityZero (selector expr : FExpr) : BaseConstraint :=
  gate selector <| assertZero expr

/-- Canonical transition-gated equality constraint. -/
def transitionEq (selector lhs rhs : FExpr) : BaseConstraint :=
  whenTransition <| gate selector <| assertEq lhs rhs

/-- Canonical transition-gated zero constraint. -/
def transitionZero (selector expr : FExpr) : BaseConstraint :=
  whenTransition <| gate selector <| assertZero expr

/-- Element-selection flag `f_i` for the supplied index bits. -/
def valueSelectionFlag (idx0Expr idx1Expr : FExpr) (i : ValueIndex) : FExpr :=
  match i.val with
  | 0 => FExpr.times (oneMinus idx1Expr) (oneMinus idx0Expr)
  | 1 => FExpr.times (oneMinus idx1Expr) idx0Expr
  | 2 => FExpr.times idx1Expr (oneMinus idx0Expr)
  | _ => FExpr.times idx1Expr idx0Expr

/-- Rust `c_i = is_read + (1 - is_read) * (1 - is_word) * (1 - f_i)`. -/
def valueConstraintFlag
    (isReadExpr isWordExpr idx0Expr idx1Expr : FExpr)
    (i : ValueIndex) : FExpr :=
  let isWriteExpr := oneMinus isReadExpr
  let isElementExpr := oneMinus isWordExpr
  let selected := valueSelectionFlag idx0Expr idx1Expr i
  FExpr.plus isReadExpr <|
    FExpr.times isWriteExpr <|
      FExpr.times isElementExpr (oneMinus selected)

/-- Next-row value-lane constraint flag `c_i`. -/
def nextValueConstraintFlag (i : ValueIndex) : FExpr :=
  valueConstraintFlag isReadNext isWordNext idx0Next idx1Next i

/-- Context delta `ctx' - ctx`. -/
def ctxDelta : FExpr := FExpr.minus ctxNext ctx

/-- Word-address delta `word_addr' - word_addr`. -/
def addrDelta : FExpr := FExpr.minus wordAddrNext wordAddr

/-- Clock delta `clk' - clk`. -/
def clkDelta : FExpr := FExpr.minus clkNext clk

/-- Rust branch flag `n0 = (ctx' - ctx) * d_inv'`. -/
def n0 : FExpr := FExpr.times ctxDelta dInvNext

/-- Rust branch flag `n1 = (word_addr' - word_addr) * d_inv'`. -/
def n1 : FExpr := FExpr.times addrDelta dInvNext

/-- Next-row delta reconstructed from the 16-bit limbs `d0'` and `d1'`. -/
def deltaFromLimbsNext : FExpr :=
  FExpr.plus (FExpr.times d1Next twoPow16) d0Next

/-- Rust monotonicity term
`n0 * ctx_delta + (1 - n0) * (n1 * addr_delta + (1 - n1) * clk_delta)`. -/
def computedDelta : FExpr :=
  FExpr.plus
    (FExpr.times n0 ctxDelta)
    (FExpr.times (oneMinus n0) <|
      FExpr.plus
        (FExpr.times n1 addrDelta)
        (FExpr.times (oneMinus n1) clkDelta))

/-- Expected next-row same-context/word flag `(1 - n0) * (1 - n1)`. -/
def sameCtxWordFlagExpected : FExpr :=
  FExpr.times (oneMinus n0) (oneMinus n1)

/-- Read-only gate factor `1 - clk_delta * d_inv'`. -/
def clkNoChange : FExpr := oneMinus (FExpr.times clkDelta dInvNext)

/-- Current-row write selector `1 - is_read`. -/
def isWrite : FExpr := oneMinus isRead

/-- Next-row write selector `1 - is_read'`. -/
def isWriteNext : FExpr := oneMinus isReadNext

/-- Sum of current-row and next-row write selectors. -/
def anyWrite : FExpr := FExpr.plus isWrite isWriteNext

/-- Canonical AIR binary constraint for `is_read`. -/
def isReadBinary : BaseConstraint :=
  integrityZero memoryFlag <|
    FExpr.times isRead (FExpr.minus isRead one)

/-- Canonical AIR binary constraint for `is_word`. -/
def isWordBinary : BaseConstraint :=
  integrityZero memoryFlag <|
    FExpr.times isWord (FExpr.minus isWord one)

/-- Canonical AIR binary constraint for `idx0`. -/
def idx0Binary : BaseConstraint :=
  integrityZero memoryFlag <|
    FExpr.times idx0 (FExpr.minus idx0 one)

/-- Canonical AIR binary constraint for `idx1`. -/
def idx1Binary : BaseConstraint :=
  integrityZero memoryFlag <|
    FExpr.times idx1 (FExpr.minus idx1 one)

/-- Canonical AIR word-access constraint `is_word * idx0 = 0`. -/
def wordAccessIdx0Zero : BaseConstraint :=
  integrityZero (FExpr.times memoryFlag isWord) idx0

/-- Canonical AIR word-access constraint `is_word * idx1 = 0`. -/
def wordAccessIdx1Zero : BaseConstraint :=
  integrityZero (FExpr.times memoryFlag isWord) idx1

/-- Canonical AIR first-memory-row zeroing constraint for `v'[i]`. -/
def firstRowValueZero (i : ValueIndex) : BaseConstraint :=
  transitionZero flagNextRowFirstMemory <|
    FExpr.times (nextValueConstraintFlag i) (valueNext i)

/-- Canonical AIR binary constraint for `n0`. -/
def n0Binary : BaseConstraint :=
  transitionZero flagMemoryActiveNotLast <|
    FExpr.times n0 (FExpr.minus n0 one)

/-- Canonical AIR constraint `!n0 => ctx' - ctx = 0`. -/
def ctxDeltaWhenNotN0 : BaseConstraint :=
  transitionZero flagMemoryActiveNotLast <|
    FExpr.times (oneMinus n0) ctxDelta

/-- Canonical AIR binary constraint for `n1` when `n0 = 0`. -/
def n1BinaryWhenSameContext : BaseConstraint :=
  transitionZero flagMemoryActiveNotLast <|
    FExpr.times (oneMinus n0) <|
      FExpr.times n1 (FExpr.minus n1 one)

/-- Canonical AIR constraint `!n0 * !n1 => word_addr' - word_addr = 0`. -/
def addrDeltaWhenSameContextAndWord : BaseConstraint :=
  transitionZero flagMemoryActiveNotLast <|
    FExpr.times (FExpr.times (oneMinus n0) (oneMinus n1)) addrDelta

/-- Canonical AIR delta-limb decomposition constraint. -/
def deltaDecomposition : BaseConstraint :=
  transitionEq flagMemoryActiveNotLast computedDelta deltaFromLimbsNext

/-- Canonical AIR next-row same-context/word flag update. -/
def sameCtxWordFlagUpdate : BaseConstraint :=
  transitionEq flagMemoryActiveNotLast sameCtxWordFlagNext sameCtxWordFlagExpected

/-- Canonical AIR read-only constraint for repeated same-clock same-word access. -/
def sameCtxWordReadonly : BaseConstraint :=
  transitionZero flagMemoryActiveNotLast <|
    FExpr.times sameCtxWordFlagNext <|
      FExpr.times clkNoChange anyWrite

/-- Canonical AIR value-consistency constraint for `v'[i]`. -/
def valueConsistency (i : ValueIndex) : BaseConstraint :=
  transitionZero flagMemoryActiveNotLast <|
    FExpr.times (nextValueConstraintFlag i) <|
      FExpr.minus (valueNext i) (FExpr.times sameCtxWordFlagNext (value i))

/-- Canonical first-memory-row zeroing constraints in Rust assertion order. -/
def firstRowValueZeroes : BaseConstraintSet :=
  List.ofFn fun i : ValueIndex => firstRowValueZero i

/-- Canonical value-consistency constraints in Rust assertion order. -/
def valueConsistencyConstraints : BaseConstraintSet :=
  List.ofFn fun i : ValueIndex => valueConsistency i

/-- Canonical memory-chiplet base constraints in Rust assertion order. -/
def base : BaseConstraintSet := allOf <|
  [isReadBinary, isWordBinary, idx0Binary, idx1Binary,
   wordAccessIdx0Zero, wordAccessIdx1Zero] ++
    firstRowValueZeroes ++
    [n0Binary, ctxDeltaWhenNotN0,
     n1BinaryWhenSameContext, addrDeltaWhenSameContextAndWord,
     deltaDecomposition, sameCtxWordFlagUpdate, sameCtxWordReadonly] ++
    valueConsistencyConstraints

private def memoryCols
    (s0Val s1Val s2Val isReadVal isWordVal ctxVal wordVal idx0Val idx1Val clkVal
     v0 v1 v2 v3 d0Val d1Val dInvVal fScwVal : Felt)
    (j : MainCol) : Felt :=
  match j.val with
  | 51 => s0Val
  | 52 => s1Val
  | 53 => s2Val
  | 54 => isReadVal
  | 55 => isWordVal
  | 56 => ctxVal
  | 57 => wordVal
  | 58 => idx0Val
  | 59 => idx1Val
  | 60 => clkVal
  | 61 => v0
  | 62 => v1
  | 63 => v2
  | 64 => v3
  | 65 => d0Val
  | 66 => d1Val
  | 67 => dInvVal
  | 68 => fScwVal
  | _ => 0

private def bitwiseStub : MainCol → Felt :=
  memoryCols 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0

private def goodEntryRow : AirRow := {
  curr := bitwiseStub
  next := memoryCols 1 1 0 1 1 9 4 0 0 7 0 0 0 0 0 0 0 0
  isTransition := 1
}

private def badEntryRow : AirRow := {
  curr := bitwiseStub
  next := memoryCols 1 1 0 1 1 9 4 0 0 7 0 0 5 0 0 0 0 0
  isTransition := 1
}

private def goodSameWordReadRow : AirRow := {
  curr := memoryCols 1 1 0 1 1 9 4 0 0 7 10 11 12 13 0 0 0 0
  next := memoryCols 1 1 0 1 1 9 4 0 0 8 10 11 12 13 1 0 1 1
  isTransition := 1
}

private def badSameWordReadRow : AirRow := {
  curr := memoryCols 1 1 0 1 1 9 4 0 0 7 10 11 12 13 0 0 0 0
  next := memoryCols 1 1 0 1 1 9 4 0 0 8 10 11 99 13 1 0 1 1
  isTransition := 1
}

private def goodAddressAdvanceRow : AirRow := {
  curr := memoryCols 1 1 0 1 1 9 4 0 0 7 10 11 12 13 0 0 0 0
  next := memoryCols 1 1 0 1 1 9 5 0 0 8 0 0 0 0 1 0 1 0
  isTransition := 1
}

private def badAddressAdvanceRow : AirRow := {
  curr := memoryCols 1 1 0 1 1 9 4 0 0 7 10 11 12 13 0 0 0 0
  next := memoryCols 1 1 0 1 1 9 5 0 0 8 0 0 0 0 2 0 1 0
  isTransition := 1
}

#eval checkBase goodEntryRow base
#eval checkBase badEntryRow base
#eval checkBase goodSameWordReadRow base
#eval checkBase badSameWordReadRow base
#eval checkBase goodAddressAdvanceRow base
#eval checkBase badAddressAdvanceRow base

end MidenLean.AIR.Semantics.Subsystems.ChipletMemory
