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
  numLocals : Nat
  body : List Op

/-- Wrap a raw op list as an anonymous procedure with no declared locals.
    This is a Phase 1 compatibility shim while generated procedures are still `List Op`. -/
abbrev Procedure.ofOps (body : List Op) : Procedure :=
  { name := "<anonymous>", numLocals := 0, body }

/-- Wrap a raw op list as a named procedure with an explicit local count.
    This is used by manual proof environments until generated code is regenerated.
    Defined as `def` (not `abbrev`) so that `simp`/`dsimp` do not auto-unfold it;
    use `execProcedure_ofNameOps` to normalize `execProcedure` calls instead. -/
def Procedure.ofNameOps (name : String) (numLocals : Nat) (body : List Op) : Procedure :=
  { name, numLocals, body }

instance : Coe (List Op) Procedure where
  coe := Procedure.ofOps

/-- A module: a collection of named procedures. -/
structure Module where
  name : String
  procedures : List Procedure

/-- Look up a procedure by name in a list of procedures. -/
def Procedure.lookup (procs : List Procedure) (name : String) : Option Procedure :=
  procs.find? (fun p => p.name == name)

end MidenLean
