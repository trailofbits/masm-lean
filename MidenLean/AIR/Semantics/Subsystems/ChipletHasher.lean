import MidenLean.AIR.Semantics.Subsystems.ChipletSelectors
/-!
# Hasher Chiplet AIR Implementation Layer

This file encodes the canonical hasher-chiplet main-trace AIR slice backed by
`air/src/constraints/chiplets/hasher/{mod,flags,selectors,state,merkle,periodic}.rs`.

The shared chiplet trace begins at `CHIPLETS_OFFSET = 51`. The hasher chiplet is
active when the top-level chiplet selector satisfies `s0 = 0`. Rust overlays the
hasher-specific mode selectors onto the next three shared selector columns, and
the canonical layout used here is:

- chiplet activity selector: `col 51`
- hasher selector `s0 = col 52`
- hasher selector `s1 = col 53`
- hasher selector `s2 = col 54`
- unused shared selector slot: `col 55`
- Poseidon2 state `h[0..11] = cols 55..66`
- Merkle node index `i = col 67`

The hasher consumes periodic columns `0..17`:

- `cycle_row_0`, `cycle_row_30`, `cycle_row_31`
- `p2_is_external`, `p2_is_internal`
- `ark_ext[0..11]`
- `ark_int`

Rust enforces exactly 62 base constraints in this order:

1. 12 init-linear Poseidon2 constraints.
2. 12 external-round Poseidon2 constraints.
3. 12 internal-round Poseidon2 constraints.
4. 3 selector booleanity constraints.
5. 4 selector consistency constraints.
6. 4 ABP capacity-preservation constraints.
7. 1 output-index constraint.
8. 2 Merkle index constraints.
9. 12 Merkle absorb-state constraints.
-/

namespace MidenLean.AIR.Semantics.Subsystems.ChipletHasher

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder
open MidenLean.AIR.Semantics.Check

/-- Shared chiplet trace offset `CHIPLETS_OFFSET = 51`. -/
abbrev chipletsOffset : Nat :=
  MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.chipletsOffset

/-- First hasher-state column (`col 55`). -/
abbrev hasherStateOffset : Nat := chipletsOffset + 4

/-- Poseidon2 state-lane index `0..11`. -/
abbrev LaneIndex := Fin 12

/-- Digest/rate/capacity sub-lane index `0..3`. -/
abbrev WordIndex := Fin 4

/-- Convenient typed lane literal. -/
def lane (n : Nat) (h : n < 12 := by decide) : LaneIndex := ⟨n, h⟩

/-- Convenient typed word-lane literal. -/
def word (n : Nat) (h : n < 4 := by decide) : WordIndex := ⟨n, h⟩

/-- Periodic column `cycle_row_0 = periodic[0]`. -/
def pCycleRow0 : PeriodicCol := ⟨0, by decide⟩

/-- Periodic column `cycle_row_30 = periodic[1]`. -/
def pCycleRow30 : PeriodicCol := ⟨1, by decide⟩

/-- Periodic column `cycle_row_31 = periodic[2]`. -/
def pCycleRow31 : PeriodicCol := ⟨2, by decide⟩

/-- Periodic column `p2_is_external = periodic[3]`. -/
def pIsExternal : PeriodicCol := ⟨3, by decide⟩

/-- Periodic column `p2_is_internal = periodic[4]`. -/
def pIsInternal : PeriodicCol := ⟨4, by decide⟩

/-- Periodic column `ark_ext[i] = periodic[5 + i]`. -/
def pArkExtCol (i : LaneIndex) : PeriodicCol := ⟨5 + i.val, by
  have hlt : 5 + i.val < 5 + 12 := Nat.add_lt_add_left i.is_lt 5
  exact lt_of_lt_of_le hlt (by decide)
⟩

/-- Periodic column `ark_int = periodic[17]`. -/
def pArkInt : PeriodicCol := ⟨17, by decide⟩

/-- Current-row hasher selector `s0` (`col 52`). -/
def sel0Col : MainCol := ⟨chipletsOffset + 1, by decide⟩

/-- Current-row hasher selector `s1` (`col 53`). -/
def sel1Col : MainCol := ⟨chipletsOffset + 2, by decide⟩

/-- Current-row hasher selector `s2` (`col 54`). -/
def sel2Col : MainCol := ⟨chipletsOffset + 3, by decide⟩

/-- Current-row state lane `h[i]` (`cols 55..66`). -/
def stateCol (i : LaneIndex) : MainCol := ⟨hasherStateOffset + i.val, by
  have hlt : hasherStateOffset + i.val < hasherStateOffset + 12 :=
    Nat.add_lt_add_left i.is_lt hasherStateOffset
  exact lt_of_lt_of_le hlt (by decide)
⟩

/-- Current-row Merkle node index (`col 67`). -/
def nodeIndexCol : MainCol := ⟨hasherStateOffset + 12, by decide⟩

/-- Top-level chiplet selector `s0` deciding whether the hasher is active. -/
abbrev chipletSel0 : FExpr :=
  MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.s0

/-- Current-row hasher-active flag `1 - chipletSel0`. -/
abbrev hasherFlag : FExpr :=
  MidenLean.AIR.Semantics.Subsystems.ChipletSelectors.hasherChipletFlag

/-- Current-row periodic marker `cycle_row_0`. -/
def cycleRow0 : FExpr := FExpr.periodic pCycleRow0

/-- Current-row periodic marker `cycle_row_30`. -/
def cycleRow30 : FExpr := FExpr.periodic pCycleRow30

/-- Current-row periodic marker `cycle_row_31`. -/
def cycleRow31 : FExpr := FExpr.periodic pCycleRow31

/-- Current-row periodic selector `p2_is_external`. -/
def isExternal : FExpr := FExpr.periodic pIsExternal

/-- Current-row periodic selector `p2_is_internal`. -/
def isInternal : FExpr := FExpr.periodic pIsInternal

/-- Current-row external round constant `ark_ext[i]`. -/
def arkExt (i : LaneIndex) : FExpr := FExpr.periodic (pArkExtCol i)

/-- Current-row internal round constant `ark_int`. -/
def arkInt : FExpr := FExpr.periodic pArkInt

/-- Current-row hasher selector `s0`. -/
def sel0 : FExpr := FExpr.curr sel0Col

/-- Current-row hasher selector `s1`. -/
def sel1 : FExpr := FExpr.curr sel1Col

/-- Current-row hasher selector `s2`. -/
def sel2 : FExpr := FExpr.curr sel2Col

/-- Next-row hasher selector `s0'`. -/
def sel0Next : FExpr := FExpr.next sel0Col

/-- Next-row hasher selector `s1'`. -/
def sel1Next : FExpr := FExpr.next sel1Col

/-- Next-row hasher selector `s2'`. -/
def sel2Next : FExpr := FExpr.next sel2Col

/-- Current-row state lane `h[i]`. -/
def state (i : LaneIndex) : FExpr := FExpr.curr (stateCol i)

/-- Next-row state lane `h'[i]`. -/
def stateNext (i : LaneIndex) : FExpr := FExpr.next (stateCol i)

/-- Current-row Merkle node index `i`. -/
def nodeIndex : FExpr := FExpr.curr nodeIndexCol

/-- Next-row Merkle node index `i'`. -/
def nodeIndexNext : FExpr := FExpr.next nodeIndexCol

/-- Constant `0`. -/
def zero : FExpr := FExpr.const 0

/-- Constant `1`. -/
def one : FExpr := FExpr.const 1

/-- Constant `2`. -/
def two : FExpr := FExpr.const 2

/-- Canonical complement expression `1 - expr`. -/
def oneMinus (expr : FExpr) : FExpr := FExpr.minus one expr

/-- Double an AIR expression. -/
def double (expr : FExpr) : FExpr := FExpr.plus expr expr

/-- Quadruple an AIR expression. -/
def quadruple (expr : FExpr) : FExpr := double (double expr)

/-- Square an AIR expression. -/
def square (expr : FExpr) : FExpr := FExpr.times expr expr

/-- Poseidon2 S-box `x^7`. -/
def pow7 (expr : FExpr) : FExpr :=
  let x2 := square expr
  let x4 := square x2
  FExpr.times expr (FExpr.times x2 x4)

/-- Canonical integrity-gated zero constraint. -/
def integrityZero (selector expr : FExpr) : BaseConstraint :=
  gate selector <| assertZero expr

/-- Canonical transition-gated zero constraint. -/
def transitionZero (selector expr : FExpr) : BaseConstraint :=
  whenTransition <| gate selector <| assertZero expr

/-- Canonical transition-gated equality constraint. -/
def transitionEq (selector lhs rhs : FExpr) : BaseConstraint :=
  whenTransition <| gate selector <| assertEq lhs rhs

/-- Lift `word` index `0..3` into the first rate word `h[0..3]`. -/
def rate0Lane (i : WordIndex) : LaneIndex := ⟨i.val, by
  exact lt_of_lt_of_le i.is_lt (by decide)
⟩

/-- Lift `word` index `0..3` into the second rate word `h[4..7]`. -/
def rate1Lane (i : WordIndex) : LaneIndex := ⟨4 + i.val, by
  have hlt : 4 + i.val < 4 + 4 := Nat.add_lt_add_left i.is_lt 4
  exact lt_of_lt_of_le hlt (by decide)
⟩

/-- Lift `word` index `0..3` into the capacity word `h[8..11]`. -/
def capacityLane (i : WordIndex) : LaneIndex := ⟨8 + i.val, by
  have hlt : 8 + i.val < 8 + 4 := Nat.add_lt_add_left i.is_lt 8
  exact lt_of_lt_of_le hlt (by decide)
⟩

/-- Current-row digest lane `h[i]` for `i = 0..3`. -/
def digest (i : WordIndex) : FExpr := state (rate0Lane i)

/-- Next-row rate0 lane `h'[i]` for `i = 0..3`. -/
def rate0Next (i : WordIndex) : FExpr := stateNext (rate0Lane i)

/-- Current-row capacity lane `h[8 + i]`. -/
def capacity (i : WordIndex) : FExpr := state (capacityLane i)

/-- Next-row rate1 lane `h'[4 + i]`. -/
def rate1Next (i : WordIndex) : FExpr := stateNext (rate1Lane i)

/-- Next-row capacity lane `h'[8 + i]`. -/
def capacityNext (i : WordIndex) : FExpr := stateNext (capacityLane i)

/-- Sum all 12 state lanes. -/
def sumLanes (lanes : LaneIndex → FExpr) : FExpr :=
  (List.ofFn fun i : LaneIndex => lanes i).foldl FExpr.plus zero

/-- Poseidon2 internal-round diagonal coefficient `MAT_DIAG[i]`. -/
def matDiag (i : LaneIndex) : FExpr :=
  match i.val with
  | 0 => FExpr.const 0xc3b6c08e23ba9300
  | 1 => FExpr.const 0xd84b5de94a324fb6
  | 2 => FExpr.const 0x0d0c371c5b35b84f
  | 3 => FExpr.const 0x7964f570e7188037
  | 4 => FExpr.const 0x5daf18bbd996604b
  | 5 => FExpr.const 0x6743bc47b9595257
  | 6 => FExpr.const 0x5528b9362c59bb70
  | 7 => FExpr.const 0xac45e25b7127b68b
  | 8 => FExpr.const 0xa2077d7dfbb606b5
  | 9 => FExpr.const 0xf3faac6faee378ae
  | 10 => FExpr.const 0x0c6388b51545e883
  | _ => FExpr.const 0xd27dbb6944917b60

/-- Apply the `M4` matrix used inside the external linear layer. -/
def matmulM4 (input : WordIndex → FExpr) : WordIndex → FExpr :=
  let a := input (word 0)
  let b := input (word 1)
  let c := input (word 2)
  let d := input (word 3)
  let t0 := FExpr.plus a b
  let t1 := FExpr.plus c d
  let t2 := FExpr.plus (double b) t1
  let t3 := FExpr.plus (double d) t0
  let t4 := FExpr.plus (quadruple t1) t3
  let t5 := FExpr.plus (quadruple t0) t2
  let out0 := FExpr.plus t3 t5
  let out1 := t5
  let out2 := FExpr.plus t2 t4
  let out3 := t4
  fun i =>
    match i.val with
    | 0 => out0
    | 1 => out1
    | 2 => out2
    | _ => out3

/-- Apply the Poseidon2 external linear layer `M_E`. -/
def applyMatmulExternal (input : LaneIndex → FExpr) : LaneIndex → FExpr :=
  let b0 := matmulM4 fun i => input (rate0Lane i)
  let b1 := matmulM4 fun i => input (rate1Lane i)
  let b2 := matmulM4 fun i => input (capacityLane i)
  let stored0 :=
    FExpr.plus (b0 (word 0)) <| FExpr.plus (b1 (word 0)) (b2 (word 0))
  let stored1 :=
    FExpr.plus (b0 (word 1)) <| FExpr.plus (b1 (word 1)) (b2 (word 1))
  let stored2 :=
    FExpr.plus (b0 (word 2)) <| FExpr.plus (b1 (word 2)) (b2 (word 2))
  let stored3 :=
    FExpr.plus (b0 (word 3)) <| FExpr.plus (b1 (word 3)) (b2 (word 3))
  fun i =>
    match i.val with
    | 0 => FExpr.plus (b0 (word 0)) stored0
    | 1 => FExpr.plus (b0 (word 1)) stored1
    | 2 => FExpr.plus (b0 (word 2)) stored2
    | 3 => FExpr.plus (b0 (word 3)) stored3
    | 4 => FExpr.plus (b1 (word 0)) stored0
    | 5 => FExpr.plus (b1 (word 1)) stored1
    | 6 => FExpr.plus (b1 (word 2)) stored2
    | 7 => FExpr.plus (b1 (word 3)) stored3
    | 8 => FExpr.plus (b2 (word 0)) stored0
    | 9 => FExpr.plus (b2 (word 1)) stored1
    | 10 => FExpr.plus (b2 (word 2)) stored2
    | _ => FExpr.plus (b2 (word 3)) stored3

/-- Apply the Poseidon2 internal linear layer `M_I`. -/
def applyMatmulInternal (input : LaneIndex → FExpr) : LaneIndex → FExpr :=
  let total := sumLanes input
  fun i => FExpr.plus (FExpr.times (input i) (matDiag i)) total

/-- Init-linear expected next state `M_E(h)`. -/
def expectedInit (i : LaneIndex) : FExpr := applyMatmulExternal state i

/-- External-round input `S-box(h + ark_ext)`. -/
def externalRoundInput (i : LaneIndex) : FExpr := pow7 (FExpr.plus (state i) (arkExt i))

/-- External-round expected next state `M_E(S-box(h + ark_ext))`. -/
def expectedExternal (i : LaneIndex) : FExpr := applyMatmulExternal externalRoundInput i

/-- Internal-round input with lane 0 replaced by `(h0 + ark_int)^7`. -/
def internalRoundInput (i : LaneIndex) : FExpr :=
  match i.val with
  | 0 => pow7 (FExpr.plus (state i) arkInt)
  | _ => state i

/-- Internal-round expected next state `M_I(tmp_int)`. -/
def expectedInternal (i : LaneIndex) : FExpr := applyMatmulInternal internalRoundInput i

/-- Merkle direction bit `b = i - 2*i'`. -/
def directionBit : FExpr := FExpr.minus nodeIndex (FExpr.times two nodeIndexNext)

/-- Merkle start flag `MP` on cycle row 0. -/
def fMp : FExpr :=
  FExpr.times cycleRow0 <| FExpr.times sel0 <| FExpr.times (oneMinus sel1) sel2

/-- Merkle verify-old flag `MV` on cycle row 0. -/
def fMv : FExpr :=
  FExpr.times cycleRow0 <| FExpr.times sel0 <| FExpr.times sel1 (oneMinus sel2)

/-- Merkle verify-new flag `MU` on cycle row 0. -/
def fMu : FExpr :=
  FExpr.times cycleRow0 <| FExpr.times sel0 <| FExpr.times sel1 sel2

/-- Linear-hash absorb flag `ABP` on cycle row 31. -/
def fAbp : FExpr :=
  FExpr.times cycleRow31 <| FExpr.times sel0 <| FExpr.times (oneMinus sel1) (oneMinus sel2)

/-- Merkle absorb flag `MPA` on cycle row 31. -/
def fMpa : FExpr :=
  FExpr.times cycleRow31 <| FExpr.times sel0 <| FExpr.times (oneMinus sel1) sel2

/-- Merkle verify-old absorb flag `MVA` on cycle row 31. -/
def fMva : FExpr :=
  FExpr.times cycleRow31 <| FExpr.times sel0 <| FExpr.times sel1 (oneMinus sel2)

/-- Merkle verify-new absorb flag `MUA` on cycle row 31. -/
def fMua : FExpr :=
  FExpr.times cycleRow31 <| FExpr.times sel0 <| FExpr.times sel1 sel2

/-- Combined output flag `(0,0,*)` on cycle row 31. -/
def fOut : FExpr :=
  FExpr.times cycleRow31 <| FExpr.times (oneMinus sel0) (oneMinus sel1)

/-- Lookahead output flag on cycle row 30. -/
def fOutNext : FExpr :=
  FExpr.times cycleRow30 <| FExpr.times (oneMinus sel0Next) (oneMinus sel1Next)

/-- Combined Merkle-operation-active flag. -/
def fMerkleActive : FExpr :=
  FExpr.plus (FExpr.plus fMp fMv) <|
    FExpr.plus fMu (FExpr.plus fMpa (FExpr.plus fMva fMua))

/-- Combined Merkle-absorb flag on cycle row 31. -/
def fMerkleAbsorb : FExpr := FExpr.plus fMpa (FExpr.plus fMva fMua)

/-- Combined continuation flag on row 31. -/
def fContinuation : FExpr := FExpr.plus fAbp (FExpr.plus fMpa (FExpr.plus fMva fMua))

/-- Gate for init-linear permutation rows. -/
def gateInit : FExpr := FExpr.times hasherFlag cycleRow0

/-- Gate for external-round permutation rows. -/
def gateExternal : FExpr := FExpr.times hasherFlag isExternal

/-- Gate for internal-round permutation rows. -/
def gateInternal : FExpr := FExpr.times hasherFlag isInternal

/-- Gate for selector stability outside of output lookahead and output rows. -/
def gateSelectorStable : FExpr :=
  FExpr.times hasherFlag (oneMinus (FExpr.plus fOut fOutNext))

/-- Gate for selector continuation rows. -/
def gateContinuation : FExpr := FExpr.times hasherFlag fContinuation

/-- Gate for ABP capacity preservation. -/
def gateAbpCapacity : FExpr := FExpr.times hasherFlag fAbp

/-- Gate for Merkle index-shift rows. -/
def gateMerkleShift : FExpr := FExpr.times hasherFlag fMerkleActive

/-- Gate for non-shift, non-output rows where the node index must persist. -/
def gateNodeIndexHold : FExpr :=
  FExpr.times hasherFlag (oneMinus (FExpr.plus fOut fMerkleActive))

/-- Gate for Merkle absorb rows. -/
def gateMerkleAbsorb : FExpr := FExpr.times hasherFlag fMerkleAbsorb

/-- Gate for direction-bit zero absorb rows. -/
def gateMerkleAbsorbLeft : FExpr :=
  FExpr.times hasherFlag (FExpr.times fMerkleAbsorb (oneMinus directionBit))

/-- Gate for direction-bit one absorb rows. -/
def gateMerkleAbsorbRight : FExpr :=
  FExpr.times hasherFlag (FExpr.times fMerkleAbsorb directionBit)

/-- Canonical AIR init-linear permutation constraint for lane `i`. -/
def permutationInit (i : LaneIndex) : BaseConstraint :=
  transitionEq gateInit (stateNext i) (expectedInit i)

/-- Canonical AIR external-round permutation constraint for lane `i`. -/
def permutationExternal (i : LaneIndex) : BaseConstraint :=
  transitionEq gateExternal (stateNext i) (expectedExternal i)

/-- Canonical AIR internal-round permutation constraint for lane `i`. -/
def permutationInternal (i : LaneIndex) : BaseConstraint :=
  transitionEq gateInternal (stateNext i) (expectedInternal i)

/-- Canonical AIR binary constraint for hasher selector `s0`. -/
def selector0Binary : BaseConstraint :=
  integrityZero hasherFlag <| FExpr.times sel0 (FExpr.minus sel0 one)

/-- Canonical AIR binary constraint for hasher selector `s1`. -/
def selector1Binary : BaseConstraint :=
  integrityZero hasherFlag <| FExpr.times sel1 (FExpr.minus sel1 one)

/-- Canonical AIR binary constraint for hasher selector `s2`. -/
def selector2Binary : BaseConstraint :=
  integrityZero hasherFlag <| FExpr.times sel2 (FExpr.minus sel2 one)

/-- Canonical AIR selector-stability constraint for `s1`. -/
def selector1Stable : BaseConstraint :=
  transitionEq gateSelectorStable sel1Next sel1

/-- Canonical AIR selector-stability constraint for `s2`. -/
def selector2Stable : BaseConstraint :=
  transitionEq gateSelectorStable sel2Next sel2

/-- Canonical AIR continuation constraint `s0' = 0`. -/
def selectorContinuation : BaseConstraint :=
  transitionZero gateContinuation sel0Next

/-- Canonical AIR row-31 invalid-selector rejection `(1 - s0) * s1 = 0`. -/
def selectorInvalidOutput : BaseConstraint :=
  integrityZero (FExpr.times hasherFlag cycleRow31) <|
    FExpr.times (oneMinus sel0) sel1

/-- Canonical AIR ABP capacity-preservation constraint for lane `i`. -/
def abpCapacityPreserved (i : WordIndex) : BaseConstraint :=
  transitionEq gateAbpCapacity (capacityNext i) (capacity i)

/-- Canonical AIR output-index constraint `f_out * i = 0`. -/
def outputIndexZero : BaseConstraint :=
  integrityZero (FExpr.times hasherFlag fOut) nodeIndex

/-- Canonical AIR binary constraint for the Merkle direction bit. -/
def directionBitBinary : BaseConstraint :=
  transitionZero gateMerkleShift <|
    FExpr.times directionBit (FExpr.minus directionBit one)

/-- Canonical AIR node-index stability constraint away from shift/output rows. -/
def nodeIndexStable : BaseConstraint :=
  transitionEq gateNodeIndexHold nodeIndexNext nodeIndex

/-- Canonical AIR Merkle absorb capacity-reset constraint for lane `i`. -/
def merkleCapacityReset (i : WordIndex) : BaseConstraint :=
  transitionZero gateMerkleAbsorb (capacityNext i)

/-- Canonical AIR digest-placement constraint into `rate0` when `b = 0`. -/
def merkleDigestToRate0 (i : WordIndex) : BaseConstraint :=
  transitionEq gateMerkleAbsorbLeft (rate0Next i) (digest i)

/-- Canonical AIR digest-placement constraint into `rate1` when `b = 1`. -/
def merkleDigestToRate1 (i : WordIndex) : BaseConstraint :=
  transitionEq gateMerkleAbsorbRight (rate1Next i) (digest i)

/-- Canonical init-linear lane constraints in Rust assertion order. -/
def permutationInitConstraints : BaseConstraintSet :=
  List.ofFn fun i : LaneIndex => permutationInit i

/-- Canonical external-round lane constraints in Rust assertion order. -/
def permutationExternalConstraints : BaseConstraintSet :=
  List.ofFn fun i : LaneIndex => permutationExternal i

/-- Canonical internal-round lane constraints in Rust assertion order. -/
def permutationInternalConstraints : BaseConstraintSet :=
  List.ofFn fun i : LaneIndex => permutationInternal i

/-- Canonical selector booleanity constraints in Rust assertion order. -/
def selectorBooleanity : BaseConstraintSet :=
  [selector0Binary, selector1Binary, selector2Binary]

/-- Canonical selector consistency constraints in Rust assertion order. -/
def selectorConsistency : BaseConstraintSet :=
  [selector1Stable, selector2Stable, selectorContinuation, selectorInvalidOutput]

/-- Canonical ABP capacity constraints in Rust assertion order. -/
def abpCapacityConstraints : BaseConstraintSet :=
  List.ofFn fun i : WordIndex => abpCapacityPreserved i

/-- Canonical Merkle capacity-reset constraints in Rust assertion order. -/
def merkleCapacityResetConstraints : BaseConstraintSet :=
  List.ofFn fun i : WordIndex => merkleCapacityReset i

/-- Canonical Merkle left-placement constraints in Rust assertion order. -/
def merkleDigestRate0Constraints : BaseConstraintSet :=
  List.ofFn fun i : WordIndex => merkleDigestToRate0 i

/-- Canonical Merkle right-placement constraints in Rust assertion order. -/
def merkleDigestRate1Constraints : BaseConstraintSet :=
  List.ofFn fun i : WordIndex => merkleDigestToRate1 i

/-- Canonical hasher-chiplet base constraints in Rust assertion order. -/
def base : BaseConstraintSet := allOf <|
  permutationInitConstraints ++
    permutationExternalConstraints ++
    permutationInternalConstraints ++
    selectorBooleanity ++
    selectorConsistency ++
    abpCapacityConstraints ++
    [outputIndexZero, directionBitBinary, nodeIndexStable] ++
    merkleCapacityResetConstraints ++
    merkleDigestRate0Constraints ++
    merkleDigestRate1Constraints

private def zeroState : LaneIndex → Felt := fun _ => 0

private def firstLaneState (x : Felt) : LaneIndex → Felt
  | ⟨0, _⟩ => x
  | _ => 0

private def hasherCols
    (chipletSel0Val sel0Val sel1Val sel2Val : Felt)
    (stateVals : LaneIndex → Felt)
    (nodeIndexVal : Felt)
    (j : MainCol) : Felt :=
  match j.val with
  | 51 => chipletSel0Val
  | 52 => sel0Val
  | 53 => sel1Val
  | 54 => sel2Val
  | 55 => stateVals (lane 0)
  | 56 => stateVals (lane 1)
  | 57 => stateVals (lane 2)
  | 58 => stateVals (lane 3)
  | 59 => stateVals (lane 4)
  | 60 => stateVals (lane 5)
  | 61 => stateVals (lane 6)
  | 62 => stateVals (lane 7)
  | 63 => stateVals (lane 8)
  | 64 => stateVals (lane 9)
  | 65 => stateVals (lane 10)
  | 66 => stateVals (lane 11)
  | 67 => nodeIndexVal
  | _ => 0

private def hasherPeriodic
    (row0Val row30Val row31Val isExternalVal isInternalVal : Felt)
    (arkIntVal : Felt := 0)
    (arkExtVals : LaneIndex → Felt := fun _ => 0)
    (j : PeriodicCol) : Felt :=
  match j.val with
  | 0 => row0Val
  | 1 => row30Val
  | 2 => row31Val
  | 3 => isExternalVal
  | 4 => isInternalVal
  | 5 => arkExtVals (lane 0)
  | 6 => arkExtVals (lane 1)
  | 7 => arkExtVals (lane 2)
  | 8 => arkExtVals (lane 3)
  | 9 => arkExtVals (lane 4)
  | 10 => arkExtVals (lane 5)
  | 11 => arkExtVals (lane 6)
  | 12 => arkExtVals (lane 7)
  | 13 => arkExtVals (lane 8)
  | 14 => arkExtVals (lane 9)
  | 15 => arkExtVals (lane 10)
  | 16 => arkExtVals (lane 11)
  | 17 => arkIntVal
  | _ => 0

private def mkHasherRow
    (currCols nextCols : MainCol → Felt)
    (periodicVals : PeriodicCol → Felt)
    (isTransitionVal : Felt := 1) : AirRow := {
  curr := currCols
  next := nextCols
  globals := { periodic := periodicVals }
  isTransition := isTransitionVal
}

private def initLinearPeriodic : PeriodicCol → Felt :=
  hasherPeriodic 1 0 0 0 0

private def outputPeriodic : PeriodicCol → Felt :=
  hasherPeriodic 0 0 1 0 0

private def goodInitRow : AirRow :=
  mkHasherRow
    (hasherCols 0 1 0 0 zeroState 0)
    (hasherCols 0 1 0 0 zeroState 0)
    initLinearPeriodic

private def badInitRow : AirRow :=
  mkHasherRow
    (hasherCols 0 1 0 0 zeroState 0)
    (hasherCols 0 1 0 0 (firstLaneState 1) 0)
    initLinearPeriodic

private def goodOutputRow : AirRow :=
  mkHasherRow
    (hasherCols 0 0 0 0 zeroState 0)
    (hasherCols 0 1 0 0 zeroState 0)
    outputPeriodic

private def badOutputRow : AirRow :=
  mkHasherRow
    (hasherCols 0 0 0 0 zeroState 7)
    (hasherCols 0 1 0 0 zeroState 0)
    outputPeriodic

#eval checkBase goodInitRow base
#eval checkBase badInitRow base
#eval checkBase goodOutputRow base
#eval checkBase badOutputRow base

end MidenLean.AIR.Semantics.Subsystems.ChipletHasher
