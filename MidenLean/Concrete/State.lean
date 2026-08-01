import MidenLean.Felt

/-!
# Concrete VM State

`Concrete.State`: the Miden VM state as an operand stack (head = top),
total-function memory (`Nat → Felt`, zero-initialized, following LNSym /
eth-isabelle / Cairo practice), a stack of local frames for procedure
locals, and the nondeterministic advice stack.
-/

namespace MidenLean

/-- Base address of the local-memory region. -/
def LOCAL_MEM_BASE : Nat := 2 ^ 31

/-- A local-memory frame tracking one procedure's allocation within the local-memory region. -/
structure LocalFrame where
  /-- Offset of this frame within the local-memory region (word-aligned). -/
  base : Nat
  /-- Number of locals declared by the procedure. -/
  numLocals : Nat
  /-- `numLocals` rounded up to the next multiple of 4 (word-aligned). -/
  alignedNumLocals : Nat
  deriving BEq

namespace Concrete

/-- The state of the Miden VM. -/
structure State where
  /-- The operand stack. Top of stack is the head of the list. -/
  stack : List Felt
  /-- Random access memory, 0-initialized. Addresses in [0, 2^32). -/
  memory : Nat → Felt
  /-- Stack of local-memory frames for nested procedure calls. -/
  frames : List LocalFrame
  /-- The advice stack (nondeterministic input). -/
  advice : List Felt

end Concrete

/-- Default 0-initialized memory. -/
def zeroMemory : Nat → Felt := fun _ => 0

/-- Create a state with the given stack and empty memory. -/
def Concrete.State.ofStack (s : List Felt) : Concrete.State :=
  { stack := s, memory := zeroMemory, frames := [], advice := [] }

/-- Create a state with the given stack and advice stack. -/
def Concrete.State.ofStackAdvice (s : List Felt) (adv : List Felt) : Concrete.State :=
  { stack := s, memory := zeroMemory, frames := [], advice := adv }

/-- Convert a frame-relative local index into its backing memory address. -/
def LocalFrame.localAddr (frame : LocalFrame) (idx : Nat) : Nat :=
  LOCAL_MEM_BASE + frame.base + idx

/-- Write a single felt to memory at the given address. -/
def Concrete.State.writeMemory (s : Concrete.State) (addr : Nat) (v : Felt) : Concrete.State :=
  { s with memory := fun a => if a = addr then v else s.memory a }

/-- Get the absolute memory address of the current frame's local slot `idx`. -/
def Concrete.State.localAddr? (s : Concrete.State) (idx : Nat) : Option Nat :=
  match s.frames with
  | frame :: _ =>
      if idx < frame.numLocals then
        some (frame.localAddr idx)
      else
        none
  | [] => none

/-- Read a single felt from the current frame's local memory. -/
def Concrete.State.readLocal? (s : Concrete.State) (idx : Nat) : Option Felt := do
  let addr ← s.localAddr? idx
  pure (s.memory addr)

/-- Write a single felt to the current frame's local memory. -/
def Concrete.State.writeLocal? (s : Concrete.State) (idx : Nat) (v : Felt) : Option Concrete.State := do
  let addr ← s.localAddr? idx
  pure (s.writeMemory addr v)

/-- Update just the stack. -/
def Concrete.State.withStack (s : Concrete.State) (stk : List Felt) : Concrete.State :=
  { s with stack := stk }

/-- Update just the advice stack. -/
def Concrete.State.withAdvice (s : Concrete.State) (adv : List Felt) : Concrete.State :=
  { s with advice := adv }

end MidenLean
