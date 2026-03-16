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

/-- Default 0-initialized memory. -/
def zeroMemory : Nat → Felt := fun _ => 0

/-- Create a state with the given stack and empty memory. -/
def MidenState.ofStack (s : List Felt) : MidenState :=
  { stack := s, memory := zeroMemory, locals := zeroMemory, advice := [] }

/-- Create a state with the given stack and advice stack. -/
def MidenState.ofStackAdvice (s : List Felt) (adv : List Felt) : MidenState :=
  { stack := s, memory := zeroMemory, locals := zeroMemory, advice := adv }

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

end MidenLean
