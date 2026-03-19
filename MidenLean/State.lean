import MidenLean.Felt

namespace MidenLean

/-- The state of the Miden VM. -/
structure MidenState where
  /-- The operand stack. Top of stack is the head of the list. -/
  stack : List Felt
  /-- Random access memory, 0-initialized. Addresses in [0, 2^32). -/
  memory : Nat → Felt
  /-- Procedure-local memory, indexed by local slot. -/
  locals : Nat → Felt
  /-- The advice stack (nondeterministic input). -/
  advice : List Felt
  /-- Emitted event IDs (most recent first). -/
  events : List Felt := []

/-- Default 0-initialized memory. -/
def zeroMemory : Nat → Felt := fun _ => 0

/-- Create a state with the given stack and empty memory. -/
def MidenState.ofStack (s : List Felt) : MidenState :=
  { stack := s, memory := zeroMemory, locals := zeroMemory, advice := [], events := [] }

/-- Create a state with the given stack and advice stack. -/
def MidenState.ofStackAdvice (s : List Felt) (adv : List Felt) : MidenState :=
  { stack := s, memory := zeroMemory, locals := zeroMemory, advice := adv, events := [] }

/-- Write a single felt to memory at the given address. -/
def MidenState.writeMemory (s : MidenState) (addr : Nat) (v : Felt) : MidenState :=
  { s with memory := fun a => if a = addr then v else s.memory a }

/-- Write a single felt to local memory at the given index. -/
def MidenState.writeLocal (s : MidenState) (idx : Nat) (v : Felt) : MidenState :=
  { s with locals := fun i => if i = idx then v else s.locals i }

/-- Update just the stack. -/
def MidenState.withStack (s : MidenState) (stk : List Felt) : MidenState :=
  { s with stack := stk }

/-- Update just the advice stack. -/
def MidenState.withAdvice (s : MidenState) (adv : List Felt) : MidenState :=
  { s with advice := adv }

/-- Minimum stack depth in the Miden VM. The Rust VM
    auto-pads to this depth with zeros. -/
def MIN_STACK_DEPTH : Nat := 16

/-- Maximum stack depth in the Miden VM. -/
def MAX_STACK_DEPTH : Nat := 2 ^ 16

/-- Pad a stack to at least MIN_STACK_DEPTH with zeros. -/
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
    memory := zeroMemory,
    locals := zeroMemory,
    advice := [],
    events := [] }

end MidenLean
