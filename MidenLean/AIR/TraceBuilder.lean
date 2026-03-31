import MidenLean.AIR.Frame
import MidenLean.AIR.StackArith

/-!
# Symbolic Trace Builder

Automates construction of AIR trace witnesses for completeness proofs.

Given a sequence of VM operations and a symbolic initial stack, this module:
1. Symbolically executes each operation to compute the next-row stack
2. Computes the required helper register values (e.g., h0 for Eq)
3. Assembles the sequence of Frames into a trace
4. Provides `simp` lemmas that discharge constraint proof obligations by `rfl`

## Design

Each operation is modeled as a function `(Fin 16 → Felt) → (Fin 16 → Felt) × (Fin 6 → Felt)`
that takes the current stack and returns (next_stack, helpers). The trace builder
chains these to produce a list of Frames where consistency holds by construction.
-/

namespace MidenLean.AIR.TraceBuilder

open MidenLean

-- ============================================================================
-- Stack update helpers
-- ============================================================================

/-- Update a single position in a stack function. -/
def updateAt (stk : Fin 16 → Felt) (pos : Fin 16) (val : Felt) : Fin 16 → Felt :=
  fun i => if i = pos then val else stk i

/-- Right-shift the stack: s'[0] = newTop, s'[i+1] = s[i] for i < 15. -/
def rightShift (stk : Fin 16 → Felt) (newTop : Felt) : Fin 16 → Felt :=
  fun i => if i = 0 then newTop else stk ⟨i.val - 1, by omega⟩

/-- Left-shift the stack: s'[i] = s[i+1] for i < 15, s'[15] = fill. -/
def leftShift (stk : Fin 16 → Felt) (fill : Felt := 0) : Fin 16 → Felt :=
  fun i => if h_bound : i.val < 15 then stk ⟨i.val + 1, Nat.add_lt_of_lt_sub h_bound⟩ else fill

/-- Transition for a binary op which consumes the top two stack elements and
    pushes `result` as the new top. -/
def binaryReduce (stk : Fin 16 → Felt) (result : Felt) (fill : Felt := 0) : Fin 16 → Felt :=
  updateAt (leftShift stk fill) 0 result

/-- Swap positions 0 and 1, keep everything else. -/
def swapTop (stk : Fin 16 → Felt) : Fin 16 → Felt :=
  fun i => if i = 0 then stk 1 else if i = 1 then stk 0 else stk i

/-- Zero helpers. -/
def zeroHelpers : Fin 6 → Felt := fun _ => 0

-- ============================================================================
-- Per-operation symbolic execution
-- ============================================================================

/-- Pad: push 0, right-shift. -/
def execPad (stk : Fin 16 → Felt) : (Fin 16 → Felt) × (Fin 6 → Felt) :=
  (rightShift stk 0, zeroHelpers)

/-- Eq: compare s[0] with s[1], produce boolean result, left-shift.
    Helper h0 = if s[0] = s[1] then 0 else (s[0] - s[1])⁻¹.
    `fill` models Rust's overflow-aware position-15 restore on left shift. -/
def execEqSymWithFill (stk : Fin 16 → Felt) (fill : Felt) : (Fin 16 → Felt) × (Fin 6 → Felt) :=
  let s0 := stk 0
  let s1 := stk 1
  let result := if s0 = s1 then Felt.ofNat 1 else Felt.ofNat 0
  let helper := if s0 = s1 then (0 : Felt) else (s0 - s1)⁻¹
  let newStk := binaryReduce stk result fill
  (newStk, fun i => if i = 0 then helper else 0)

/-- Eq with empty-overflow behavior at position 15. -/
def execEqSym (stk : Fin 16 → Felt) : (Fin 16 → Felt) × (Fin 6 → Felt) :=
  execEqSymWithFill stk 0

/-- Swap: exchange positions 0 and 1. -/
def execSwapSym (stk : Fin 16 → Felt) : (Fin 16 → Felt) × (Fin 6 → Felt) :=
  (swapTop stk, zeroHelpers)

/-- And: boolean AND of s[0] and s[1], left-shift.
    `fill` models Rust's overflow-aware position-15 restore on left shift. -/
def execAndSymWithFill (stk : Fin 16 → Felt) (fill : Felt) : (Fin 16 → Felt) × (Fin 6 → Felt) :=
  let s0 := stk 0
  let s1 := stk 1
  let result := if s0 = Felt.ofNat 1 ∧ s1 = Felt.ofNat 1
    then Felt.ofNat 1 else Felt.ofNat 0
  let newStk := binaryReduce stk result fill
  (newStk, zeroHelpers)

/-- And with empty-overflow behavior at position 15. -/
def execAndSym (stk : Fin 16 → Felt) : (Fin 16 → Felt) × (Fin 6 → Felt) :=
  execAndSymWithFill stk 0

-- ============================================================================
-- Trace construction
-- ============================================================================

/-- A single symbolic operation. -/
inductive SymOp where
  | pad
  | eq
  | swap
  | and
  deriving Repr

/-- Execute a symbolic operation on a stack. -/
def execSymOp (op : SymOp) (stk : Fin 16 → Felt) : (Fin 16 → Felt) × (Fin 6 → Felt) :=
  match op with
  | .pad => execPad stk
  | .eq => execEqSym stk
  | .swap => execSwapSym stk
  | .and => execAndSym stk

/-- Build a Frame from a current stack and an operation. -/
def buildFrame (stk : Fin 16 → Felt) (op : SymOp) : Frame :=
  let (stk', helpers) := execSymOp op stk
  { s := stk, s' := stk', h := helpers }

/-- Build an EQ frame with an explicit restored value for position 15. -/
def buildEqFrame (stk : Fin 16 → Felt) (fill : Felt := 0) : Frame :=
  let (stk', helpers) := execEqSymWithFill stk fill
  { s := stk, s' := stk', h := helpers }

/-- Build an AND frame with an explicit restored value for position 15. -/
def buildAndFrame (stk : Fin 16 → Felt) (fill : Felt := 0) : Frame :=
  let (stk', helpers) := execAndSymWithFill stk fill
  { s := stk, s' := stk', h := helpers }

/-- Build a sequence of frames from an initial stack and operation list.
    Returns the frames and the final stack. -/
def buildTrace (stk : Fin 16 → Felt) : List SymOp → List Frame × (Fin 16 → Felt)
  | [] => ([], stk)
  | op :: ops =>
    let frame := buildFrame stk op
    let (rest_frames, final_stk) := buildTrace frame.s' ops
    (frame :: rest_frames, final_stk)

-- ============================================================================
-- Key lemmas: buildFrame consistency
-- ============================================================================

/-- The current-row stack of buildFrame is the input stack. -/
@[simp] theorem buildFrame_s (stk : Fin 16 → Felt) (op : SymOp) :
    (buildFrame stk op).s = stk := rfl

/-- The next-row stack of buildFrame is the symbolic execution result. -/
@[simp] theorem buildFrame_s' (stk : Fin 16 → Felt) (op : SymOp) :
    (buildFrame stk op).s' = (execSymOp op stk).1 := rfl

/-- The helper registers of buildFrame come from symbolic execution. -/
@[simp] theorem buildFrame_h (stk : Fin 16 → Felt) (op : SymOp) :
    (buildFrame stk op).h = (execSymOp op stk).2 := rfl

/-- The current-row stack of `buildEqFrame` is the input stack. -/
@[simp] theorem buildEqFrame_s (stk : Fin 16 → Felt) (fill : Felt) :
    (buildEqFrame stk fill).s = stk := rfl

/-- The next-row stack of `buildEqFrame` is its symbolic execution result. -/
@[simp] theorem buildEqFrame_s' (stk : Fin 16 → Felt) (fill : Felt) :
    (buildEqFrame stk fill).s' = (execEqSymWithFill stk fill).1 := rfl

/-- The helper registers of `buildEqFrame` come from symbolic execution. -/
@[simp] theorem buildEqFrame_h (stk : Fin 16 → Felt) (fill : Felt) :
    (buildEqFrame stk fill).h = (execEqSymWithFill stk fill).2 := rfl

/-- The current-row stack of `buildAndFrame` is the input stack. -/
@[simp] theorem buildAndFrame_s (stk : Fin 16 → Felt) (fill : Felt) :
    (buildAndFrame stk fill).s = stk := rfl

/-- The next-row stack of `buildAndFrame` is its symbolic execution result. -/
@[simp] theorem buildAndFrame_s' (stk : Fin 16 → Felt) (fill : Felt) :
    (buildAndFrame stk fill).s' = (execAndSymWithFill stk fill).1 := rfl

/-- The helper registers of `buildAndFrame` come from symbolic execution. -/
@[simp] theorem buildAndFrame_h (stk : Fin 16 → Felt) (fill : Felt) :
    (buildAndFrame stk fill).h = (execAndSymWithFill stk fill).2 := rfl

-- ============================================================================
-- Simp lemmas for stack operations
-- ============================================================================

@[simp] theorem rightShift_zero (stk : Fin 16 → Felt) (v : Felt) :
    rightShift stk v 0 = v := by
  unfold rightShift; simp

@[simp] theorem rightShift_succ (stk : Fin 16 → Felt) (v : Felt) (i : Fin 15) :
    rightShift stk v ⟨i.val + 1, by omega⟩ = stk ⟨i.val, by omega⟩ := by
  unfold rightShift
  have h_ne : ¬(⟨i.val + 1, by omega⟩ : Fin 16) = (0 : Fin 16) := by
    intro h_absurd
    have := Fin.ext_iff.mp h_absurd
    simp at this
  simp only [h_ne, ↓reduceIte, Nat.add_sub_cancel]

@[simp] theorem leftShift_lt (stk : Fin 16 → Felt) (fill : Felt) (i : Fin 16)
    (h_lt : i.val < 15) :
    leftShift stk fill i = stk ⟨i.val + 1, by omega⟩ := by
  simp [leftShift, h_lt]

@[simp] theorem leftShift_last (stk : Fin 16 → Felt) (fill : Felt) :
    leftShift stk fill 15 = fill := by
  simp [leftShift]

@[simp] theorem binaryReduce_zero (stk : Fin 16 → Felt) (result fill : Felt) :
    binaryReduce stk result fill 0 = result := by
  simp [binaryReduce, updateAt]

@[simp] theorem binaryReduce_shift (stk : Fin 16 → Felt) (result fill : Felt) (i : Fin 14) :
    binaryReduce stk result fill ⟨i.val + 1, by omega⟩ = stk ⟨i.val + 2, by omega⟩ := by
  have hi : i.val < 14 := i.isLt
  have h_lt : (⟨i.val + 1, by omega⟩ : Fin 16).val < 15 := by
    change i.val + 1 < 15
    exact Nat.succ_lt_succ hi
  have h_ne : (⟨i.val + 1, by omega⟩ : Fin 16) ≠ (0 : Fin 16) := by
    intro h_eq
    have h_val := Fin.ext_iff.mp h_eq
    change i.val + 1 = 0 at h_val
    exact Nat.succ_ne_zero i.val h_val
  simp [binaryReduce, updateAt, leftShift, h_lt, h_ne]

@[simp] theorem swapTop_zero (stk : Fin 16 → Felt) :
    swapTop stk 0 = stk 1 := by simp [swapTop]

@[simp] theorem swapTop_one (stk : Fin 16 → Felt) :
    swapTop stk 1 = stk 0 := by
  unfold swapTop
  have : ¬((1 : Fin 16) = 0) := by decide
  simp [this]

@[simp] theorem swapTop_ge2 (stk : Fin 16 → Felt) (i : Fin 16) (h_ge : 2 ≤ i.val) :
    swapTop stk i = stk i := by
  unfold swapTop
  have h_ne0 : ¬(i = 0) := by intro heq; subst heq; simp at h_ge
  have h_ne1 : ¬(i = 1) := by intro heq; subst heq; simp at h_ge
  simp [h_ne0, h_ne1]

@[simp] theorem updateAt_eq (stk : Fin 16 → Felt) (pos : Fin 16) (val : Felt) :
    updateAt stk pos val pos = val := by simp [updateAt]

@[simp] theorem updateAt_ne (stk : Fin 16 → Felt) (pos i : Fin 16) (val : Felt)
    (h_ne : i ≠ pos) :
    updateAt stk pos val i = stk i := by simp [updateAt, h_ne]

-- ============================================================================
-- Builder witness lemmas
-- ============================================================================

/-- `buildFrame` for PAD pushes `0` onto the top of the visible stack. -/
theorem buildFrame_pad_zero (stk : Fin 16 → Felt) :
    (buildFrame stk .pad).s' 0 = 0 := by
  simp [buildFrame, execSymOp, execPad]

/-- `buildFrame` for PAD right-shifts the remaining visible stack. -/
theorem buildFrame_pad_shift (stk : Fin 16 → Felt) (i : Fin 15) :
    (buildFrame stk .pad).s' ⟨i.val + 1, by omega⟩ =
      (buildFrame stk .pad).s ⟨i.val, by omega⟩ := by
  simpa [buildFrame, execSymOp, execPad] using (rightShift_succ stk (0 : Felt) i)

/-- `buildFrame` for EQ satisfies the local AIR constraint. -/
theorem buildEqFrame_air (stk : Fin 16 → Felt) (fill : Felt) :
    Miden.AIR.StackArith.air_eq ((buildEqFrame stk fill).s 0) ((buildEqFrame stk fill).s 1)
      ((buildEqFrame stk fill).s' 0) ((buildEqFrame stk fill).h 0) := by
  unfold Miden.AIR.StackArith.air_eq
  by_cases heq : stk 0 = stk 1
  · refine ⟨?_, ?_⟩
    · simp [Felt.ofNat, buildEqFrame, execEqSymWithFill, binaryReduce, heq]
    · simp [Felt.ofNat, buildEqFrame, execEqSymWithFill, binaryReduce, heq]
  · refine ⟨?_, ?_⟩
    · simp [Felt.ofNat, buildEqFrame, execEqSymWithFill, binaryReduce, heq]
    · simp [Felt.ofNat, buildEqFrame, execEqSymWithFill, binaryReduce, heq,
        mul_inv_cancel₀ (sub_ne_zero.mpr heq)]

/-- `buildFrame` for EQ satisfies the local AIR constraint. -/
theorem buildFrame_eq_air (stk : Fin 16 → Felt) :
    Miden.AIR.StackArith.air_eq ((buildFrame stk .eq).s 0) ((buildFrame stk .eq).s 1)
      ((buildFrame stk .eq).s' 0) ((buildFrame stk .eq).h 0) := by
  simpa [buildFrame, execSymOp, execEqSym] using buildEqFrame_air stk 0

/-- `buildFrame` for EQ also satisfies the visible left-shift behavior. -/
theorem buildEqFrame_shift (stk : Fin 16 → Felt) (fill : Felt) (i : Fin 14) :
    (buildEqFrame stk fill).s' ⟨i.val + 1, by omega⟩ =
      (buildEqFrame stk fill).s ⟨i.val + 2, by omega⟩ := by
  simpa [buildEqFrame, execEqSymWithFill, binaryReduce] using
    (binaryReduce_shift stk (if stk 0 = stk 1 then Felt.ofNat 1 else Felt.ofNat 0) fill i)

/-- `buildFrame` for EQ also satisfies the visible left-shift behavior. -/
theorem buildFrame_eq_shift (stk : Fin 16 → Felt) (i : Fin 14) :
    (buildFrame stk .eq).s' ⟨i.val + 1, by omega⟩ =
      (buildFrame stk .eq).s ⟨i.val + 2, by omega⟩ := by
  simpa [buildFrame, execSymOp, execEqSym] using buildEqFrame_shift stk 0 i

/-- The EQ witness produced by `buildFrame` is always boolean. -/
theorem buildEqFrame_result_bool (stk : Fin 16 → Felt) (fill : Felt) :
    (buildEqFrame stk fill).s' 0 = Felt.ofNat 0 ∨ (buildEqFrame stk fill).s' 0 = Felt.ofNat 1 := by
  by_cases heq : stk 0 = stk 1
  · right
    simp [buildEqFrame, execEqSymWithFill, binaryReduce, heq]
  · left
    simp [buildEqFrame, execEqSymWithFill, binaryReduce, heq]

/-- The EQ witness produced by `buildFrame` is always boolean. -/
theorem buildFrame_eq_result_bool (stk : Fin 16 → Felt) :
    (buildFrame stk .eq).s' 0 = Felt.ofNat 0 ∨ (buildFrame stk .eq).s' 0 = Felt.ofNat 1 := by
  simpa [buildFrame, execSymOp, execEqSym] using buildEqFrame_result_bool stk 0

/-- `buildEqFrame` restores the explicit fill value into position 15. -/
theorem buildEqFrame_last (stk : Fin 16 → Felt) (fill : Felt) :
    (buildEqFrame stk fill).s' 15 = fill := by
  have h_ne : (15 : Fin 16) ≠ (0 : Fin 16) := by decide
  simp [buildEqFrame, execEqSymWithFill, binaryReduce, updateAt, h_ne]

/-- `buildFrame` for SWAP places the old second stack item on top. -/
theorem buildFrame_swap_zero (stk : Fin 16 → Felt) :
    (buildFrame stk .swap).s' 0 = (buildFrame stk .swap).s 1 := by
  simp [buildFrame, execSymOp, execSwapSym]

/-- `buildFrame` for SWAP places the old top stack item in position `1`. -/
theorem buildFrame_swap_one (stk : Fin 16 → Felt) :
    (buildFrame stk .swap).s' 1 = (buildFrame stk .swap).s 0 := by
  simp [buildFrame, execSymOp, execSwapSym]

/-- `buildFrame` for SWAP preserves the visible stack below depth `1`. -/
theorem buildFrame_swap_rest (stk : Fin 16 → Felt) (i : Fin 14) :
    (buildFrame stk .swap).s' ⟨i.val + 2, by omega⟩ =
      (buildFrame stk .swap).s ⟨i.val + 2, by omega⟩ := by
  have h_ge : 2 ≤ (⟨i.val + 2, by omega⟩ : Fin 16).val := by
    change 2 ≤ i.val + 2
    simpa [Nat.add_assoc] using Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le i.val))
  simpa [buildFrame, execSymOp, execSwapSym] using
    (swapTop_ge2 stk ⟨i.val + 2, by omega⟩ h_ge)

/-- `buildFrame` for AND satisfies the local AIR constraint when its inputs are boolean. -/
theorem buildAndFrame_air_of_bool (stk : Fin 16 → Felt) (fill : Felt)
    (hs0 : stk 0 = Felt.ofNat 0 ∨ stk 0 = Felt.ofNat 1)
    (hs1 : stk 1 = Felt.ofNat 0 ∨ stk 1 = Felt.ofNat 1) :
    Miden.AIR.StackArith.air_and ((buildAndFrame stk fill).s 0) ((buildAndFrame stk fill).s 1)
      ((buildAndFrame stk fill).s' 0) := by
  unfold Miden.AIR.StackArith.air_and
  rcases hs0 with hs0 | hs0 <;> rcases hs1 with hs1 | hs1 <;>
    simp [buildAndFrame, execAndSymWithFill, binaryReduce, Felt.ofNat, hs0, hs1]

/-- `buildFrame` for AND satisfies the local AIR constraint when its inputs are boolean. -/
theorem buildFrame_and_air_of_bool (stk : Fin 16 → Felt)
    (hs0 : stk 0 = Felt.ofNat 0 ∨ stk 0 = Felt.ofNat 1)
    (hs1 : stk 1 = Felt.ofNat 0 ∨ stk 1 = Felt.ofNat 1) :
    Miden.AIR.StackArith.air_and ((buildFrame stk .and).s 0) ((buildFrame stk .and).s 1)
      ((buildFrame stk .and).s' 0) := by
  simpa [buildFrame, execSymOp, execAndSym] using buildAndFrame_air_of_bool stk 0 hs0 hs1

/-- `buildFrame` for AND also satisfies the visible left-shift behavior. -/
theorem buildAndFrame_shift (stk : Fin 16 → Felt) (fill : Felt) (i : Fin 14) :
    (buildAndFrame stk fill).s' ⟨i.val + 1, by omega⟩ =
      (buildAndFrame stk fill).s ⟨i.val + 2, by omega⟩ := by
  simpa [buildAndFrame, execAndSymWithFill, binaryReduce] using
    (binaryReduce_shift stk
      (if stk 0 = Felt.ofNat 1 ∧ stk 1 = Felt.ofNat 1 then Felt.ofNat 1 else Felt.ofNat 0)
      fill i)

/-- `buildFrame` for AND also satisfies the visible left-shift behavior. -/
theorem buildFrame_and_shift (stk : Fin 16 → Felt) (i : Fin 14) :
    (buildFrame stk .and).s' ⟨i.val + 1, by omega⟩ =
      (buildFrame stk .and).s ⟨i.val + 2, by omega⟩ := by
  simpa [buildFrame, execSymOp, execAndSym] using buildAndFrame_shift stk 0 i

/-- `buildAndFrame` restores the explicit fill value into position 15. -/
theorem buildAndFrame_last (stk : Fin 16 → Felt) (fill : Felt) :
    (buildAndFrame stk fill).s' 15 = fill := by
  have h_ne : (15 : Fin 16) ≠ (0 : Fin 16) := by decide
  simp [buildAndFrame, execAndSymWithFill, binaryReduce, updateAt, h_ne]

end MidenLean.AIR.TraceBuilder
