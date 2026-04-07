import MidenLean.AIR.Semantics.Subsystems.ChipletSelectors
/-!
# Bitwise Chiplet AIR Implementation Layer

This file encodes the canonical bitwise-chiplet main-trace AIR slice backed by
`air/src/constraints/chiplets/bitwise.rs`.

The chiplet segment begins at `CHIPLETS_OFFSET = 51`. The bitwise chiplet is
active when the shared selector prefix satisfies `s0 = 1` and `s1 = 0`, so
Rust addresses its local trace with
`BITWISE_TRACE_OFFSET = CHIPLETS_OFFSET + 2 = 53`. The resulting layout is:

- shared selectors: `s0 = col 51`, `s1 = col 52`
- `op_flag = col 53`
- `a = col 54`
- `b = col 55`
- `a_bits[0..3] = cols 56..59`
- `b_bits[0..3] = cols 60..63`
- `prev_output = col 64`
- `output = col 65`

The periodic columns reuse the hasher prefix `0..17`, so the bitwise cycle
markers are:

- `k_first = periodic[18]`
- `k_transition = periodic[19]`

Rust enforces 17 base constraints in this order:

1. `op_flag` is binary.
2. `op_flag` is stable across non-final rows of the 8-row cycle.
3. `a_bits[0..3]` are binary.
4. `b_bits[0..3]` are binary.
5. On the first cycle row, `a`, `b`, and `prev_output` are initialized from the
   current nibble decomposition.
6. On transition rows, `a'` and `b'` append the next nibble.
7. On transition rows, `prev_output' = output`.
8. On every active row, `output` aggregates either nibble-AND or nibble-XOR
   depending on `op_flag`.
-/

namespace MidenLean.AIR.Semantics.Subsystems.ChipletBitwise

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder
open MidenLean.AIR.Semantics.Check

/-- Shared chiplet trace offset `CHIPLETS_OFFSET = 51`. -/
abbrev chipletsOffset : Nat :=
  MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.chipletsOffset

/-- Rust `BITWISE_TRACE_OFFSET = CHIPLETS_OFFSET + 2 = 53`. -/
abbrev bitwiseTraceOffset : Nat := chipletsOffset + 2

/-- First `a_bits` column (`col 56`). -/
abbrev aBitsOffset : Nat := chipletsOffset + 5

/-- First `b_bits` column (`col 60`). -/
abbrev bBitsOffset : Nat := aBitsOffset + 4

/-- Typed bit index `0..3`. -/
abbrev BitIndex := Fin 4

/-- Periodic column `k_first = periodic[18]`. -/
def pBitwiseKFirst : PeriodicCol := ⟨18, by decide⟩

/-- Periodic column `k_transition = periodic[19]`. -/
def pBitwiseKTransition : PeriodicCol := ⟨19, by decide⟩

/-- Current-row bitwise operation selector `op_flag` (`col 53`). -/
def opFlagCol : MainCol := ⟨bitwiseTraceOffset, by decide⟩

/-- Current-row aggregated input `a` (`col 54`). -/
def aCol : MainCol := ⟨bitwiseTraceOffset + 1, by decide⟩

/-- Current-row aggregated input `b` (`col 55`). -/
def bCol : MainCol := ⟨bitwiseTraceOffset + 2, by decide⟩

/-- Current-row `a_bits[i]` (`cols 56..59`). -/
def aBitCol (i : BitIndex) : MainCol := ⟨aBitsOffset + i.val, by
  have hlt : aBitsOffset + i.val < aBitsOffset + 4 :=
    Nat.add_lt_add_left i.is_lt aBitsOffset
  exact lt_of_lt_of_le hlt (by decide)
⟩

/-- Current-row `b_bits[i]` (`cols 60..63`). -/
def bBitCol (i : BitIndex) : MainCol := ⟨bBitsOffset + i.val, by
  have hlt : bBitsOffset + i.val < bBitsOffset + 4 :=
    Nat.add_lt_add_left i.is_lt bBitsOffset
  exact lt_of_lt_of_le hlt (by decide)
⟩

/-- Current-row previous-output column (`col 64`). -/
def prevOutputCol : MainCol := ⟨chipletsOffset + 13, by decide⟩

/-- Current-row output column (`col 65`). -/
def outputCol : MainCol := ⟨chipletsOffset + 14, by decide⟩

/-- Current-row chiplet-active flag `s0 * (1 - s1)`. -/
abbrev bitwiseFlag : FExpr :=
  MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.bitwiseChipletFlag

/-- Current-row periodic marker `k_first`. -/
def kFirst : FExpr := FExpr.periodic pBitwiseKFirst

/-- Current-row periodic marker `k_transition`. -/
def kTransition : FExpr := FExpr.periodic pBitwiseKTransition

/-- Current-row `op_flag`. -/
def opFlag : FExpr := FExpr.curr opFlagCol

/-- Next-row `op_flag'`. -/
def opFlagNext : FExpr := FExpr.next opFlagCol

/-- Current-row aggregated input `a`. -/
def a : FExpr := FExpr.curr aCol

/-- Next-row aggregated input `a'`. -/
def aNext : FExpr := FExpr.next aCol

/-- Current-row aggregated input `b`. -/
def b : FExpr := FExpr.curr bCol

/-- Next-row aggregated input `b'`. -/
def bNext : FExpr := FExpr.next bCol

/-- Current-row `a_bits[i]`. -/
def aBit (i : BitIndex) : FExpr := FExpr.curr (aBitCol i)

/-- Next-row `a_bits'[i]`. -/
def aBitNext (i : BitIndex) : FExpr := FExpr.next (aBitCol i)

/-- Current-row `b_bits[i]`. -/
def bBit (i : BitIndex) : FExpr := FExpr.curr (bBitCol i)

/-- Next-row `b_bits'[i]`. -/
def bBitNext (i : BitIndex) : FExpr := FExpr.next (bBitCol i)

/-- Current-row `prev_output`. -/
def prevOutput : FExpr := FExpr.curr prevOutputCol

/-- Next-row `prev_output'`. -/
def prevOutputNext : FExpr := FExpr.next prevOutputCol

/-- Current-row `output`. -/
def output : FExpr := FExpr.curr outputCol

/-- Constant `1`. -/
def one : FExpr := FExpr.const 1

/-- Constant `16`. -/
def sixteen : FExpr := FExpr.const 16

/-- First-row gate `k_first * bitwise_flag`. -/
def gateFirst : FExpr := FExpr.times kFirst bitwiseFlag

/-- Transition gate `k_transition * bitwise_flag`. -/
def gateTransition : FExpr := FExpr.times kTransition bitwiseFlag

/-- Canonical transition-gated equality constraint. -/
def transitionEq (selector lhs rhs : FExpr) : BaseConstraint :=
  whenTransition <| gate selector <| assertEq lhs rhs

/-- Canonical integrity-gated equality constraint. -/
def integrityEq (selector lhs rhs : FExpr) : BaseConstraint :=
  gate selector <| assertEq lhs rhs

/-- Canonical integrity-gated zero constraint. -/
def integrityZero (selector expr : FExpr) : BaseConstraint :=
  gate selector <| assertZero expr

/-- Double one AIR expression. -/
def double (expr : FExpr) : FExpr := FExpr.plus expr expr

/-- Aggregate 4 little-endian bits into a nibble using the same Horner layout as
Rust `aggregate_limbs`. -/
def aggregateBits (bits : BitIndex → FExpr) : FExpr :=
  let acc32 := FExpr.plus (double (bits 3)) (bits 2)
  let acc321 := FExpr.plus (double acc32) (bits 1)
  FExpr.plus (double acc321) (bits 0)

/-- Nibble AND aggregation matching Rust `compute_limb_and`. -/
def nibbleAnd (lhs rhs : BitIndex → FExpr) : FExpr :=
  let acc32 := FExpr.plus (double (FExpr.times (lhs 3) (rhs 3))) (FExpr.times (lhs 2) (rhs 2))
  let acc321 := FExpr.plus (double acc32) (FExpr.times (lhs 1) (rhs 1))
  FExpr.plus (double acc321) (FExpr.times (lhs 0) (rhs 0))

/-- Nibble XOR aggregation matching Rust `compute_limb_xor`. -/
def nibbleXor (lhs rhs : BitIndex → FExpr) : FExpr :=
  let xorBit (i : BitIndex) :=
    let andBit := FExpr.times (lhs i) (rhs i)
    FExpr.minus (FExpr.plus (lhs i) (rhs i)) (double andBit)
  let acc32 := FExpr.plus (double (xorBit 3)) (xorBit 2)
  let acc321 := FExpr.plus (double acc32) (xorBit 1)
  FExpr.plus (double acc321) (xorBit 0)

/-- Canonical AIR binary constraint for `op_flag`. -/
def opFlagBinary : BaseConstraint :=
  integrityZero bitwiseFlag <|
    FExpr.times opFlag (FExpr.minus opFlag one)

/-- Canonical AIR stability constraint for `op_flag`. -/
def opFlagStability : BaseConstraint :=
  transitionEq gateTransition opFlagNext opFlag

/-- Canonical AIR binary constraint for `a_bits[i]`. -/
def aBitBinary (i : BitIndex) : BaseConstraint :=
  integrityZero bitwiseFlag <|
    FExpr.times (aBit i) (FExpr.minus (aBit i) one)

/-- Canonical AIR binary constraint for `b_bits[i]`. -/
def bBitBinary (i : BitIndex) : BaseConstraint :=
  integrityZero bitwiseFlag <|
    FExpr.times (bBit i) (FExpr.minus (bBit i) one)

/-- Canonical AIR first-row constraint `a = aggregate(a_bits)`. -/
def firstRowA : BaseConstraint :=
  integrityEq gateFirst a (aggregateBits aBit)

/-- Canonical AIR first-row constraint `b = aggregate(b_bits)`. -/
def firstRowB : BaseConstraint :=
  integrityEq gateFirst b (aggregateBits bBit)

/-- Canonical AIR first-row constraint `prev_output = 0`. -/
def firstRowPrevOutput : BaseConstraint :=
  gate gateFirst <| assertZero prevOutput

/-- Canonical AIR transition constraint
`a' = 16 * a + aggregate(a_bits')`. -/
def inputTransitionA : BaseConstraint :=
  transitionEq gateTransition aNext <|
    FExpr.plus (FExpr.times a sixteen) (aggregateBits aBitNext)

/-- Canonical AIR transition constraint
`b' = 16 * b + aggregate(b_bits')`. -/
def inputTransitionB : BaseConstraint :=
  transitionEq gateTransition bNext <|
    FExpr.plus (FExpr.times b sixteen) (aggregateBits bBitNext)

/-- Canonical AIR transition constraint `prev_output' = output`. -/
def outputPrevTransition : BaseConstraint :=
  transitionEq gateTransition prevOutputNext output

/-- Canonical AIR expected output expression
`16 * prev_output + and + op_flag * (xor - and)`. -/
def expectedOutput : FExpr :=
  let andResult := nibbleAnd aBit bBit
  let xorResult := nibbleXor aBit bBit
  FExpr.plus
    (FExpr.times prevOutput sixteen)
    (FExpr.plus andResult (FExpr.times opFlag (FExpr.minus xorResult andResult)))

/-- Canonical AIR output aggregation constraint. -/
def outputAggregation : BaseConstraint :=
  integrityEq bitwiseFlag output expectedOutput

/-- Canonical `a_bits[0..3]` binary constraints in Rust assertion order. -/
def aBitBinaries : BaseConstraintSet :=
  List.ofFn fun i : BitIndex => aBitBinary i

/-- Canonical `b_bits[0..3]` binary constraints in Rust assertion order. -/
def bBitBinaries : BaseConstraintSet :=
  List.ofFn fun i : BitIndex => bBitBinary i

/-- Canonical bitwise-chiplet base constraints in Rust assertion order. -/
def base : BaseConstraintSet := allOf <|
  [opFlagBinary, opFlagStability] ++
    aBitBinaries ++
    bBitBinaries ++
    [firstRowA, firstRowB, firstRowPrevOutput,
     inputTransitionA, inputTransitionB,
     outputPrevTransition, outputAggregation]

private def bitwiseCols
    (s0Val s1Val opVal aVal bVal
     a0 a1 a2 a3 b0 b1 b2 b3
     prevVal outVal : Felt)
    (j : MainCol) : Felt :=
  match j.val with
  | 51 => s0Val
  | 52 => s1Val
  | 53 => opVal
  | 54 => aVal
  | 55 => bVal
  | 56 => a0
  | 57 => a1
  | 58 => a2
  | 59 => a3
  | 60 => b0
  | 61 => b1
  | 62 => b2
  | 63 => b3
  | 64 => prevVal
  | 65 => outVal
  | _ => 0

private def bitwisePeriodic
    (kFirstVal kTransitionVal : Felt)
    (j : PeriodicCol) : Felt :=
  match j.val with
  | 18 => kFirstVal
  | 19 => kTransitionVal
  | _ => 0

private def goodAndFirstRow : AirRow := {
  curr := bitwiseCols 1 0 0 5 3 1 0 1 0 1 1 0 0 0 1
  next := bitwiseCols 1 0 0 82 52 0 1 0 0 0 0 1 0 1 0
  globals := {
    periodic := bitwisePeriodic 1 1
  }
  isTransition := 1
}

private def badOpFlagRow : AirRow := {
  curr := bitwiseCols 1 0 2 5 3 1 0 1 0 1 1 0 0 0 1
  next := bitwiseCols 1 0 2 82 52 0 1 0 0 0 0 1 0 1 0
  globals := {
    periodic := bitwisePeriodic 1 1
  }
  isTransition := 1
}

#eval checkBase goodAndFirstRow base
#eval checkBase badOpFlagRow base

end MidenLean.AIR.Semantics.Subsystems.ChipletBitwise
