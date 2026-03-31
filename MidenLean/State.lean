import MidenLean.Felt

namespace MidenLean

/-- Base address of the local-memory region. -/
def LOCAL_MEM_BASE : Nat := 2 ^ 31

/-- Address of the frame pointer cell (VM-reserved). -/
def FMP_ADDR : Nat := 2 ^ 32 - 1

/-- A local-memory frame tracking one procedure's allocation within the local-memory region. -/
structure LocalFrame where
  /-- Offset of this frame within the local-memory region (word-aligned). -/
  base : Nat
  /-- Number of locals declared by the procedure. -/
  numLocals : Nat
  /-- `numLocals` rounded up to the next multiple of 4 (word-aligned). -/
  alignedNumLocals : Nat
  deriving BEq

/-- The state of the Miden VM. -/
structure MidenState where
  /-- The operand stack. Top of stack is the head of the list. -/
  stack : List Felt
  /-- Random access memory, 0-initialized. Addresses in [0, 2^32). -/
  memory : Nat → Felt
  /-- Stack of local-memory frames for nested procedure calls. -/
  frames : List LocalFrame
  /-- The advice stack (nondeterministic input). -/
  advice : List Felt

/-- Default 0-initialized memory. -/
def zeroMemory : Nat → Felt := fun _ => 0

/-- Create a state with the given stack and empty memory. -/
def MidenState.ofStack (s : List Felt) : MidenState :=
  { stack := s, memory := zeroMemory, frames := [], advice := [] }

/-- Create a state with the given stack and advice stack. -/
def MidenState.ofStackAdvice (s : List Felt) (adv : List Felt) : MidenState :=
  { stack := s, memory := zeroMemory, frames := [], advice := adv }

/-- Convert a frame-relative local index into its backing memory address. -/
def LocalFrame.localAddr (frame : LocalFrame) (idx : Nat) : Nat :=
  LOCAL_MEM_BASE + frame.base + idx

/-- Write a single felt to memory at the given address. -/
def MidenState.writeMemory (s : MidenState) (addr : Nat) (v : Felt) : MidenState :=
  { s with memory := fun a => if a = addr then v else s.memory a }

/-- Get the absolute memory address of the current frame's local slot `idx`. -/
def MidenState.localAddr? (s : MidenState) (idx : Nat) : Option Nat :=
  match s.frames with
  | frame :: _ =>
      if idx < frame.numLocals then
        some (frame.localAddr idx)
      else
        none
  | [] => none

/-- Read a single felt from the current frame's local memory. -/
def MidenState.readLocal? (s : MidenState) (idx : Nat) : Option Felt := do
  let addr ← s.localAddr? idx
  pure (s.memory addr)

/-- Write a single felt to the current frame's local memory. -/
def MidenState.writeLocal? (s : MidenState) (idx : Nat) (v : Felt) : Option MidenState := do
  let addr ← s.localAddr? idx
  pure (s.writeMemory addr v)

/-- Update just the stack. -/
def MidenState.withStack (s : MidenState) (stk : List Felt) : MidenState :=
  { s with stack := stk }

/-- Update just the advice stack. -/
def MidenState.withAdvice (s : MidenState) (adv : List Felt) : MidenState :=
  { s with advice := adv }

end MidenLean
