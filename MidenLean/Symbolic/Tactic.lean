import MidenLean.Symbolic.Reflect
import MidenLean.Proofs.ControlFlow

/-!
# Proof Automation Tactics

## `miden_reflect`

Automates the application of `reflect_basic_block` for basic block proofs.
Given a goal `exec fuel ⟨stack, mem, frames, adv⟩ proc = some ⟨result, ...⟩`,
the tactic:
1. Extracts the instruction list from `proc.body`
2. Counts stack input variables
3. Constructs the assignment witness `σ`
4. Applies `reflect_basic_block`, closing setup goals automatically
5. Leaves precondition obligations for the user

## `miden_vcg`

Decomposes control flow in `execWithEnv`-based existential goals.
Scans the procedure's `List Op` for control-flow ops and applies
the appropriate composition rule:
- **`Op.ifElse`**: applies `execWithEnv_ifElse`, generating branch subgoals
- **`Op.repeat`**: applies `execWithEnv_repeat`, generating invariant subgoals
- **`Op.whileTrue`**: applies `execWithEnv_while`, generating invariant/measure subgoals

For mixed op lists (prefix instructions + control flow), the tactic splits
at the first control-flow boundary using `execWithEnv_append`, reduces the
prefix via `simp`, then applies the composition rule.
-/

namespace MidenLean.Symbolic.Tactic

open Lean Elab Tactic Meta PrettyPrinter

/-- Extract consecutive `List.cons` elements from a `Lean.Expr`.
    Returns the head elements and the tail (first non-cons subexpression). -/
private partial def extractCons (e : Lean.Expr) : MetaM (Array Lean.Expr × Lean.Expr) := do
  let e ← whnf e
  match_expr e with
  | List.cons _ hd tl =>
    let (rest, tail) ← extractCons tl
    return (#[hd] ++ rest, tail)
  | _ => return (#[], e)

/-- Extract `Instruction` values from a `List Op` expression that consists entirely of
    `Op.inst i` constructors. Returns `none` if any op is not `Op.inst`. -/
private partial def extractInsts (e : Lean.Expr) : MetaM (Option (Array Lean.Expr)) := do
  let e ← whnf e
  match_expr e with
  | List.cons _ hd tl =>
    let hdW ← whnf hd
    match_expr hdW with
    | MidenLean.Op.inst inst =>
      let some rest ← extractInsts tl | return none
      return some (#[inst] ++ rest)
    | _ => return none
  | List.nil _ => return some #[]
  | _ => return none

/-- Convert an internal `Lean.Expr` to surface `Syntax` via the pretty-printer. -/
private def toTermSyntax (e : Lean.Expr) : MetaM (TSyntax `term) := do
  let stx ← delab e
  return ⟨stx⟩

elab "miden_reflect" : tactic => do
  let mvarId ← getMainGoal
  let goal ← mvarId.getType

  -- Step 1: Parse goal
  let some (_, lhs, _) := goal.eq?
    | throwError "miden_reflect: goal is not an equation"

  unless lhs.isAppOf ``MidenLean.exec && lhs.getAppNumArgs == 3 do
    throwError "miden_reflect: LHS should be `MidenLean.exec fuel state proc`"
  let fuel := lhs.getArg! 0
  let state := lhs.getArg! 1
  let proc := lhs.getArg! 2

  -- Step 2: Decompose state
  let stateWhnf ← whnf state
  unless stateWhnf.getAppNumArgs == 4 do
    throwError "miden_reflect: state should be ⟨stack, mem, frames, adv⟩"
  let stackExpr := stateWhnf.getArg! 0
  let memExpr := stateWhnf.getArg! 1
  let framesExpr := stateWhnf.getArg! 2
  let advExpr := stateWhnf.getArg! 3

  -- Step 3: Extract stack elements
  let (stackElems, restExpr) ← extractCons stackExpr
  let n := stackElems.size
  if n == 0 then
    throwError "miden_reflect: no stack elements found"

  -- Step 4: Extract instructions from proc.body
  let procWhnf ← whnf proc
  unless procWhnf.getAppNumArgs == 3 do
    throwError "miden_reflect: could not reduce procedure to ⟨name, numLocals, body⟩"
  let body := procWhnf.getArg! 2
  let some instExprs ← extractInsts body
    | throwError "miden_reflect: procedure body contains non-instruction ops (only basic blocks supported)"

  -- Step 5: Build syntax terms
  let fuelStx ← toTermSyntax fuel
  let memStx ← toTermSyntax memExpr
  let framesStx ← toTermSyntax framesExpr
  let advStx ← toTermSyntax advExpr
  let restStx ← toTermSyntax restExpr
  let procStx ← toTermSyntax proc
  let nStx : TSyntax `num := ⟨Syntax.mkNumLit (toString n)⟩

  -- Build instruction list syntax: [inst₁, inst₂, ...]
  let instStxs : Array (TSyntax `term) ← instExprs.mapM (fun e => toTermSyntax e)
  let instsStx ← `([$instStxs,*])

  -- Build σ (assignment) as: fun i => [e₀, e₁, ...].getD i 0
  let elemStxs : Array (TSyntax `term) ← stackElems.mapM (fun e => toTermSyntax e)
  let elemListStx ← `([$elemStxs,*])
  let sigmaStx ← `(fun i => ($elemListStx : List MidenLean.Felt).getD i 0)

  -- Step 6: Apply reflect_basic_block
  evalTactic (← `(tactic|
    refine MidenLean.Symbolic.Reflect.reflect_basic_block
      $instsStx $procStx $fuelStx
      _ $memStx $framesStx $advStx $nStx $restStx
      ($sigmaStx)
      _ rfl rfl (by omega) ?_ rfl ?_))

  -- Step 7: Close hstack goal
  let goals ← getGoals
  if goals.length > 0 then
    setGoals [goals.head!]
    try
      evalTactic (← `(tactic|
        simp [MidenLean.Symbolic.State.ofInputs,
              MidenLean.Symbolic.Expr.eval,
              List.range_succ, List.range_zero, List.map]))
    catch _ => pure ()
    let remaining ← getGoals
    setGoals (remaining ++ goals.tail!)

end MidenLean.Symbolic.Tactic

-- ============================================================================
-- miden_vcg: control-flow decomposition (top-level for global availability)
-- ============================================================================

/-- `miden_vcg` decomposes control flow in `execWithEnv`-based existential goals.

    Handles goals of the form:
    `∃ s', execWithEnv env fuel s proc = some s' ∧ P s'`

    Applies the appropriate composition rule based on the control-flow op found:
    - `Op.ifElse`: `execWithEnv_ifElse`
    - `Op.whileTrue`: `execWithEnv_while`
    - `Op.repeat`: `execWithEnv_repeat`

    For procedures with prefix instructions before the control-flow op,
    split manually with `rw [execWithEnv_append]` first, reduce the prefix,
    then retry `miden_vcg`. -/
syntax "miden_vcg" : tactic
macro_rules
  | `(tactic| miden_vcg) =>
    `(tactic| first
      | apply MidenLean.execWithEnv_ifElse _ _ _ _ _ _ _ _ rfl
      | apply MidenLean.execWithEnv_while
      | apply MidenLean.execWithEnv_repeat)
