import MidenLean.Instruction

namespace MidenLean

/-- A MASM operation: either a primitive instruction or a control flow construct. -/
inductive Op where
  /-- A primitive instruction. -/
  | inst (i : Instruction)
  /-- Conditional: if.true body [else elseBody] end.
      Pops a boolean from the stack; executes thenBlk if 1, elseBlk if 0. -/
  | ifElse (thenBlk : List Op) (elseBlk : List Op)
  /-- Counter-controlled loop: repeat.count body end.
      Unrolls the body `count` times. -/
  | repeat (count : Nat) (body : List Op)
  /-- Condition-controlled loop: while.true body end.
      Pops a boolean; if 1, executes body then repeats. -/
  | whileTrue (body : List Op)

/-- A named procedure. -/
structure Procedure where
  name : String
  body : List Op

/-- A module: a collection of named procedures. -/
structure Module where
  name : String
  procedures : List Procedure

/-- Look up a procedure by name in a list of procedures. -/
def Procedure.lookup (procs : List Procedure) (name : String) : Option (List Op) :=
  procs.find? (fun p => p.name == name) |>.map (fun p => p.body)

end MidenLean
