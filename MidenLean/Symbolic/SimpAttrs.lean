import Lean
import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# Symbolic simp attribute sets

Custom attributes used by symbolic reflection automation.
-/

/-- Simp set for `miden_reflect` target canonicalization and cleanup. -/
register_simp_attr miden_reflect_norm

/-- Shared normalization set for the reflection cleanup ladders
    (`miden_finish_reflection`, `finalizeCleanupGoals`,
    `cleanupExecSummaryGoals`). Populated in `Symbolic/Reflect.lean` with the
    evaluator/state unfolds and `∧`-reassociation lemmas those ladders share,
    so the lemma list exists in exactly one place. -/
register_simp_attr miden_cleanup

namespace MidenLean.Symbolic

open Lean

/-- Persistent environment extension storing the names of theorems annotated
    with `@[miden_exec_summary]`. The reflection tactic queries this extension
    to find a callee execution summary by Procedure constant rather than
    relying on convention-based name construction. -/
initialize execSummaryExt :
    SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    name := `MidenLean.Symbolic.execSummary
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl Array.append #[]
  }

/-- `@[miden_exec_summary]` registers a theorem as a callee execution summary
    for use by `miden_vcg` and `miden_reflect`. The theorem must have an `Eq`
    conclusion of the form `execProcedure env fuel state callee = some result`,
    where `callee` is a constant referring to a `Procedure` value. -/
initialize registerBuiltinAttribute {
  name := `miden_exec_summary
  descr := "Marks a theorem as a callee execution summary for miden_vcg/miden_reflect"
  add := fun declName _stx _kind => do
    modifyEnv fun env => execSummaryExt.addEntry env declName
  applicationTime := .afterCompilation
}

/-- All theorem names currently registered with `@[miden_exec_summary]`. -/
def getExecSummaryTheorems (env : Environment) : Array Name :=
  execSummaryExt.getState env

end MidenLean.Symbolic
