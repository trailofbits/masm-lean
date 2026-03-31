import MidenLean.State

/-!
# Word-Order Specification

This module is the canonical word-order layer for the local Miden audit.

Trust boundary:

* VM instruction semantics describe how execution state changes.
* Rust accessors such as `get_stack_word(start_idx)` are a separate boundary.
* Debug / observer surfaces such as `debug.stack` are a separate boundary.

AIR or VM execution correctness does **not** imply accessor or observer correctness.
Those surfaces need their own specs and regression tests.

For local-word instructions, this Lean model assumes the instruction stream has already
passed the assembler's index validation. The ordering claims below are about execution
semantics after validation, not about front-end rejection of malformed instructions.
-/

namespace MidenLean

/-- Canonical stack representation of a word. The head of the list is the top of the stack. -/
def stackWord (e0 e1 e2 e3 : Felt) : List Felt :=
  [e0, e1, e2, e3]

/-- Canonical stack representation of a double word. -/
def stackDWord (e0 e1 e2 e3 e4 e5 e6 e7 : Felt) : List Felt :=
  [e0, e1, e2, e3, e4, e5, e6, e7]

/-- The top of the stack is a word, followed by `tail`. -/
def HasStackWord (stk : List Felt) (e0 e1 e2 e3 : Felt) (tail : List Felt) : Prop :=
  stk = stackWord e0 e1 e2 e3 ++ tail

/-- The top of the stack is a double word, followed by `tail`. -/
def HasStackDWord
    (stk : List Felt) (e0 e1 e2 e3 e4 e5 e6 e7 : Felt) (tail : List Felt) : Prop :=
  stk = stackDWord e0 e1 e2 e3 e4 e5 e6 e7 ++ tail

/-- Little-endian stack view of four consecutive elements from a source. -/
def sourceWordLe (src : Nat → Felt) (base : Nat) : List Felt :=
  stackWord (src base) (src (base + 1)) (src (base + 2)) (src (base + 3))

/-- Big-endian stack view of four consecutive elements from a source. -/
def sourceWordBe (src : Nat → Felt) (base : Nat) : List Felt :=
  stackWord (src (base + 3)) (src (base + 2)) (src (base + 1)) (src base)

/-- Write a stack word into a source in little-endian order. -/
def writeWordLe (src : Nat → Felt) (base : Nat) (e0 e1 e2 e3 : Felt) : Nat → Felt :=
  fun addr =>
    if addr = base then e0
    else if addr = base + 1 then e1
    else if addr = base + 2 then e2
    else if addr = base + 3 then e3
    else src addr

/-- Write a stack word into a source in big-endian order. -/
def writeWordBe (src : Nat → Felt) (base : Nat) (e0 e1 e2 e3 : Felt) : Nat → Felt :=
  fun addr =>
    if addr = base then e3
    else if addr = base + 1 then e2
    else if addr = base + 2 then e1
    else if addr = base + 3 then e0
    else src addr

/-- Lean-side model of the current Rust `get_stack_word(start_idx)` accessor orientation.
    Missing elements are padded with zero, matching the safe processor accessor. -/
def stackWordAccessor (stk : List Felt) (startIdx : Nat) : List Felt :=
  stackWord
    (stk.getD startIdx 0)
    (stk.getD (startIdx + 1) 0)
    (stk.getD (startIdx + 2) 0)
    (stk.getD (startIdx + 3) 0)

@[simp] theorem stackWord_append (e0 e1 e2 e3 : Felt) (tail : List Felt) :
    stackWord e0 e1 e2 e3 ++ tail = e0 :: e1 :: e2 :: e3 :: tail := by
  rfl

@[simp] theorem stackDWord_append
    (e0 e1 e2 e3 e4 e5 e6 e7 : Felt) (tail : List Felt) :
    stackDWord e0 e1 e2 e3 e4 e5 e6 e7 ++ tail =
      e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: tail := by
  rfl

@[simp] theorem stackWord_reverse (e0 e1 e2 e3 : Felt) :
    (stackWord e0 e1 e2 e3).reverse = stackWord e3 e2 e1 e0 := by
  rfl

@[simp] theorem stackDWord_reverse (e0 e1 e2 e3 e4 e5 e6 e7 : Felt) :
    (stackDWord e0 e1 e2 e3 e4 e5 e6 e7).reverse = stackDWord e7 e6 e5 e4 e3 e2 e1 e0 := by
  rfl

@[simp] theorem sourceWordBe_eq_reverse_sourceWordLe (src : Nat → Felt) (base : Nat) :
    sourceWordBe src base = (sourceWordLe src base).reverse := by
  simp [sourceWordBe, sourceWordLe]

theorem writeWordLe_eq_writeWordBe_reversed
    (src : Nat → Felt) (base : Nat) (e0 e1 e2 e3 : Felt) :
    writeWordLe src base e0 e1 e2 e3 = writeWordBe src base e3 e2 e1 e0 := by
  funext addr
  simp [writeWordLe, writeWordBe]

theorem writeWordBe_eq_reordered
    (src : Nat → Felt) (base : Nat) (e0 e1 e2 e3 : Felt) :
    (fun addr =>
      if addr = base + 3 then e0
      else if addr = base + 2 then e1
      else if addr = base + 1 then e2
      else if addr = base then e3
      else src addr) = writeWordBe src base e0 e1 e2 e3 := by
  funext addr
  by_cases h0 : addr = base
  · simp [writeWordBe, h0]
  · by_cases h1 : addr = base + 1
    · simp [writeWordBe, h1]
    · by_cases h2 : addr = base + 2
      · simp [writeWordBe, h2]
      · by_cases h3 : addr = base + 3
        · simp [writeWordBe, h3]
        · simp [writeWordBe, h0, h1, h2, h3]

theorem writeWordLe_eq_reordered
    (src : Nat → Felt) (base : Nat) (e0 e1 e2 e3 : Felt) :
    (fun addr =>
      if addr = base + 3 then e3
      else if addr = base + 2 then e2
      else if addr = base + 1 then e1
      else if addr = base then e0
      else src addr) = writeWordLe src base e0 e1 e2 e3 := by
  funext addr
  by_cases h0 : addr = base
  · simp [writeWordLe, h0]
  · by_cases h1 : addr = base + 1
    · simp [writeWordLe, h1]
    · by_cases h2 : addr = base + 2
      · simp [writeWordLe, h2]
      · by_cases h3 : addr = base + 3
        · simp [writeWordLe, h3]
        · simp [writeWordLe, h0, h1, h2, h3]

theorem stackWordAccessor_matches_top_word
    (e0 e1 e2 e3 : Felt) (tail : List Felt) :
    stackWordAccessor (stackWord e0 e1 e2 e3 ++ tail) 0 = stackWord e0 e1 e2 e3 := by
  simp [stackWordAccessor, stackWord]

theorem stackWordAccessor_matches_offset_word
    (pre : List Felt) (e0 e1 e2 e3 : Felt) (tail : List Felt) :
    stackWordAccessor (pre ++ stackWord e0 e1 e2 e3 ++ tail) pre.length =
      stackWord e0 e1 e2 e3 := by
  simp [stackWordAccessor, stackWord]

theorem stackWordAccessor_zero_pads_past_stack (e0 : Felt) :
    stackWordAccessor [e0] 0 = stackWord e0 0 0 0 := by
  simp [stackWordAccessor, stackWord]

end MidenLean
