/-
Axiom audit for the MidenLean library.

Run with:  lake env lean scripts/AxiomCheck.lean

This replaces grepping for `sorry`, which is brittle in both directions: it
matches the word in comments and docstrings (a stale comment reading
"mulsteps (sorry for now)" once broke the check), and it misses a `sorry`
reached *transitively* — a theorem whose proof term is clean but which applies
a helper lemma that is itself unproved. Asking the kernel which axioms a
declaration actually depends on catches exactly the real cases and nothing else.

Two things are checked for every declaration defined in a `MidenLean` module:

* `sorryAx` — an unproved statement. Always a failure.
* any axiom outside `expectedAxioms` — an unintended trust assumption.

`Lean.ofReduceBool` and `Lean.trustCompiler` are expected because
`MidenLean/Felt.lean` proves the Goldilocks primality `Fact` by `native_decide`,
which puts the Lean compiler in the trusted base for every `Felt`-dependent
theorem. They are listed here so that the footprint is asserted rather than
assumed: if someone removes that `native_decide`, this file should be updated
and the footprint shrinks; if someone adds a *new* source of compiler trust,
the count reported below changes and is visible in review.
-/
import MidenLean

open Lean

namespace AxiomCheck

/-- Axioms the library is known and intended to depend on. -/
def expectedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound,
   -- from the `native_decide` proof of Goldilocks primality in Felt.lean
   ``Lean.ofReduceBool, ``Lean.trustCompiler]

/-- Is this declaration defined in one of our own modules (not Mathlib etc.)? -/
def isOurs (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false          -- defined in the current file, not the library
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => (`MidenLean).isPrefixOf m
      | none => false

/-- Skip compiler-generated declarations: they inherit their axioms from the
    declaration they were generated for, so reporting them is pure noise. -/
def isInternal (n : Name) : Bool :=
  n.isInternal
    || n.hasMacroScopes
    || (`Lean).isPrefixOf n

structure Report where
  checked : Nat := 0
  sorries : Array Name := #[]
  unexpected : Array (Name × Array Name) := #[]
  /-- Declarations that carry the compiler-trust axioms, for reporting. -/
  compilerTrust : Nat := 0

def run : CoreM Report := do
  let env ← getEnv
  let expected := expectedAxioms
  let mut r : Report := {}
  for (n, _) in env.constants.toList do
    unless isOurs env n && !isInternal n do continue
    r := { r with checked := r.checked + 1 }
    let axs ← Lean.collectAxioms n
    if axs.contains ``sorryAx then
      r := { r with sorries := r.sorries.push n }
    let unexpected := axs.filter (fun a => !expected.contains a)
    unless unexpected.isEmpty do
      r := { r with unexpected := r.unexpected.push (n, unexpected) }
    if axs.contains ``Lean.ofReduceBool || axs.contains ``Lean.trustCompiler then
      r := { r with compilerTrust := r.compilerTrust + 1 }
  return r

end AxiomCheck

open AxiomCheck in
run_cmd do
  let r ← Elab.Command.liftCoreM run
  logInfo s!"axiom-checked {r.checked} declarations in MidenLean modules"
  logInfo s!"{r.compilerTrust} depend on compiler trust (native_decide via Felt.lean)"
  unless r.sorries.isEmpty do
    throwError "found {r.sorries.size} declaration(s) depending on sorryAx:\n{
      r.sorries.toList.map toString}"
  unless r.unexpected.isEmpty do
    let rendered := r.unexpected.toList.map fun (n, axs) =>
      s!"  {n}: {axs.toList.map toString}"
    throwError "found declaration(s) with unexpected axioms:\n{String.intercalate "\n" rendered}"
  logInfo "no sorryAx, no unexpected axioms"
