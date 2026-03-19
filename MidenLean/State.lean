import MidenLean.Felt

namespace MidenLean

/-- A Miden word: 4 field elements. -/
abbrev Word := Felt × Felt × Felt × Felt

/-- The zero word. -/
def Word.zero : Word := (0, 0, 0, 0)

/-- Access individual elements of a word (0-indexed). -/
def Word.get (w : Word) (i : Fin 4) : Felt :=
  match i with
  | 0 => w.1
  | 1 => w.2.1
  | 2 => w.2.2.1
  | 3 => w.2.2.2

/-- Set an individual element of a word. -/
def Word.set (w : Word) (i : Fin 4) (v : Felt) : Word :=
  match i with
  | 0 => (v, w.2.1, w.2.2.1, w.2.2.2)
  | 1 => (w.1, v, w.2.2.1, w.2.2.2)
  | 2 => (w.1, w.2.1, v, w.2.2.2)
  | 3 => (w.1, w.2.1, w.2.2.1, v)

/-- Convert a word to a list of 4 elements. -/
def Word.toList (w : Word) : List Felt :=
  [w.1, w.2.1, w.2.2.1, w.2.2.2]

/-- Default 0-initialized word-addressed memory. -/
def zeroWordMemory : Nat → Word := fun _ => Word.zero

/-- The state of the Miden VM. -/
structure MidenState where
  /-- The operand stack. Top of stack is the head of
      the list. -/
  stack : List Felt
  /-- Random access memory, word-addressed, 0-initialized.
      Addresses in [0, 2^32). Each address maps to a Word
      (4 field elements), matching the Rust VM's
      BTreeMap<u32, [Felt; 4]>. -/
  memory : Nat → Word
  /-- Procedure-local memory, word-addressed, indexed by
      local slot. Each slot stores a Word. -/
  locals : Nat → Word
  /-- The advice stack (nondeterministic input). -/
  advice : List Felt
  /-- Emitted event IDs (most recent first). -/
  events : List Felt := []

/-- Create a state with the given stack and empty memory. -/
def MidenState.ofStack (s : List Felt) : MidenState :=
  { stack := s, memory := zeroWordMemory,
    locals := zeroWordMemory, advice := [], events := [] }

/-- Create a state with the given stack and advice
    stack. -/
def MidenState.ofStackAdvice (s : List Felt)
    (adv : List Felt) : MidenState :=
  { stack := s, memory := zeroWordMemory,
    locals := zeroWordMemory, advice := adv, events := [] }

/-- Write a full word to memory at the given address. -/
def MidenState.writeMemory (s : MidenState) (addr : Nat)
    (w : Word) : MidenState :=
  { s with memory := fun a =>
    if a = addr then w else s.memory a }

/-- Write a single felt to element 0 of the word at
    the given memory address, preserving elements 1-3.
    This matches the Rust VM's mem_store behavior. -/
def MidenState.writeMemoryElem0 (s : MidenState)
    (addr : Nat) (v : Felt) : MidenState :=
  { s with memory := fun a =>
    if a = addr then
      (v, (s.memory addr).2.1,
       (s.memory addr).2.2.1, (s.memory addr).2.2.2)
    else s.memory a }

/-- Write a full word to local memory at the given
    slot index. -/
def MidenState.writeLocal (s : MidenState) (idx : Nat)
    (w : Word) : MidenState :=
  { s with locals := fun i =>
    if i = idx then w else s.locals i }

/-- Write a single felt to element 0 of the local word
    at the given slot, preserving elements 1-3. -/
def MidenState.writeLocalElem0 (s : MidenState)
    (idx : Nat) (v : Felt) : MidenState :=
  { s with locals := fun i =>
    if i = idx then
      (v, (s.locals idx).2.1,
       (s.locals idx).2.2.1, (s.locals idx).2.2.2)
    else s.locals i }

/-- Update just the stack. -/
def MidenState.withStack (s : MidenState)
    (stk : List Felt) : MidenState :=
  { s with stack := stk }

/-- Update just the advice stack. -/
def MidenState.withAdvice (s : MidenState)
    (adv : List Felt) : MidenState :=
  { s with advice := adv }

/-- Minimum stack depth in the Miden VM. The Rust VM
    auto-pads to this depth with zeros. -/
def MIN_STACK_DEPTH : Nat := 16

/-- Maximum stack depth in the Miden VM. -/
def MAX_STACK_DEPTH : Nat := 2 ^ 16

/-- Pad a stack to at least MIN_STACK_DEPTH with
    zeros. -/
def padStack (stk : List Felt) : List Felt :=
  stk ++ List.replicate (MIN_STACK_DEPTH - stk.length) 0

/-- A well-formed Miden state has stack depth in
    [MIN_STACK_DEPTH, MAX_STACK_DEPTH]. -/
def MidenState.wellFormed (s : MidenState) : Prop :=
  MIN_STACK_DEPTH ≤ s.stack.length ∧
  s.stack.length ≤ MAX_STACK_DEPTH

/-- Create a well-formed state by padding the stack. -/
def MidenState.ofStackPadded (s : List Felt) :
    MidenState :=
  { stack := padStack s,
    memory := zeroWordMemory,
    locals := zeroWordMemory,
    advice := [],
    events := [] }

end MidenLean
