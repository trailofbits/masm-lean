import MidenLean.Symbolic.Reflect
import MidenLean.Proofs.ControlFlow

/-!
# Proof Automation Tactics

## `miden_reflect`

Automates reflection for straight-line procedure proofs.
Supported goals are `exec` / `execWithEnv` equations whose procedure body is a
straight-line `List Op`. Control flow is still rejected. Procedures with
`.exec` calls are supported through `miden_reflect using Γ`, where `Γ` is a
`ReflectEnv` carrying symbolic callee summaries and soundness proofs.

Given a goal `exec fuel ⟨stack, mem, frames, adv⟩ proc = some ⟨result, ...⟩`
or `execWithEnv env fuel ⟨stack, mem, frames, adv⟩ proc = some ⟨result, ...⟩`,
the tactic:
1. Extracts the instruction list from `proc.body`
2. Canonicalizes the target to the wrapper-theorem surface
3. Applies `reflect_with_env_zero` or `reflect_with_env_locals`
4. Closes mechanical setup goals automatically
5. Leaves semantic precondition obligations for the user, if any

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

/-- Goal data extracted from an `exec` / `execWithEnv` equation. -/
private structure ReflectGoal where
  lhs : Lean.Expr
  rhs : Lean.Expr
  envExpr : Lean.Expr
  fuelExpr : Lean.Expr
  stateExpr : Lean.Expr
  procExpr : Lean.Expr
  stackExpr : Lean.Expr
  memExpr : Lean.Expr
  framesExpr : Lean.Expr
  advExpr : Lean.Expr
  stackElems : Array Lean.Expr
  restExpr : Lean.Expr
  bodyExpr : Lean.Expr
  opExprs : Array Lean.Expr
  hasExec : Bool
  useStateWrapper : Bool

/-- Extract consecutive `List.cons` elements from a `Lean.Expr`.
    Returns the head elements and the tail (first non-cons subexpression). -/
private partial def extractCons (e : Lean.Expr) : MetaM (Array Lean.Expr × Lean.Expr) := do
  let e ← whnf e
  match_expr e with
  | List.cons _ hd tl =>
    let (rest, tail) ← extractCons tl
    return (#[hd] ++ rest, tail)
  | _ => return (#[], e)

/-- Extract `Op` values from a concrete `List Op` expression. -/
private partial def extractOps (e : Lean.Expr) : MetaM (Option (Array Lean.Expr)) := do
  let e ← whnf e
  match_expr e with
  | List.cons _ hd tl =>
    let some rest ← extractOps tl | return none
    return some (#[hd] ++ rest)
  | List.nil _ => return some #[]
  | _ => return none

/-- Check whether an op is an `exec` call. -/
private def opHasExec (opExpr : Lean.Expr) : MetaM Bool := do
  let opExpr ← whnf opExpr
  match_expr opExpr with
  | MidenLean.Op.inst inst =>
      let inst ← whnf inst
      match_expr inst with
      | MidenLean.Instruction.exec _ => pure true
      | _ => pure false
  | _ => pure false

/-- Extract the `.exec` target from an op, if any. -/
private def execTargetExpr? (opExpr : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let opExpr ← whnf opExpr
  match_expr opExpr with
  | MidenLean.Op.inst inst =>
      let inst ← whnf inst
      match_expr inst with
      | MidenLean.Instruction.exec target => pure (some target)
      | _ => pure none
  | _ => pure none

/-- Build a concrete `List` expression from already elaborated elements. -/
private def mkListExpr (elemTy : Lean.Expr) (xs : List Lean.Expr) : MetaM Lean.Expr := do
  xs.foldrM
    (fun x acc => mkAppM ``List.cons #[x, acc])
    (← mkAppOptM ``List.nil #[some elemTy])

/-- Check if a Lean `Expr` is a `Nat` literal equal to zero. -/
private def isNatZero (e : Lean.Expr) : Bool :=
  e.numeral? == some 0 || e.isConstOf ``Nat.zero

/-- Check whether an expression has type `List α` for the given element type. -/
private def hasListTypeOf (e : Lean.Expr) (elemTyName : Lean.Name) : MetaM Bool := do
  let ty ← whnf (← inferType e)
  pure <|
    ty.isAppOfArity ``List 1 &&
    (ty.getArg! 0).isConstOf elemTyName

/-- Find a local hypothesis that decomposes `state.stack`. -/
private def findStackDecomposition (stateExpr : Lean.Expr) : TacticM (Array Lean.Expr × Lean.Expr) := do
  let stackProj := Lean.mkProj ``MidenLean.MidenState 0 stateExpr
  for localDecl in (← getLCtx) do
    unless localDecl.isImplementationDetail do
      match localDecl.type.eq? with
      | some (_, lhs, rhs) =>
          if ← isDefEq lhs stackProj then
            return ← extractCons rhs
          if ← isDefEq rhs stackProj then
            return ← extractCons lhs
      | none => pure ()
  throwError "miden_reflect: could not find a stack decomposition hypothesis for `state.stack`"

/-- Run a tactic against a single goal and return the remaining goals. -/
private def runOnGoal (goal : MVarId) (stx : TSyntax `tactic) : TacticM (List MVarId) := do
  if ← goal.isAssigned then
    pure []
  else
    setGoals [goal]
    evalTactic stx
    return ← getGoals

/-- Solve a goal completely with the provided tactic script. -/
private def closeGoalWith (goal : MVarId) (label : String) (stx : TSyntax `tactic) : TacticM Unit := do
  unless ← goal.isAssigned do
    let remaining ← runOnGoal goal stx
    unless remaining.isEmpty do
      let ty ← remaining[0]!.getType
      throwError "miden_reflect: failed to solve {label}:{indentExpr ty}"

/-- Apply light cleanup to remaining goals, closing trivial `hpreconds` goals. -/
private def cleanupGoals (goals : List MVarId) : TacticM (List MVarId) := do
  let mut remaining : List MVarId := []
  for goal in goals do
    unless ← goal.isAssigned do
      let rem ← runOnGoal goal (← `(tactic|
        try
          simp [miden_reflect_norm,
                and_assoc, and_left_comm, and_comm,
                MidenLean.MidenState.withStack,
                MidenLean.Symbolic.Precondition.holds,
                MidenLean.Symbolic.Expr.eval,
                MidenLean.Symbolic.Reflect.concreteAssignment,
                MidenLean.Symbolic.Reflect.concreteState,
                MidenLean.Symbolic.Reflect.concreteStateWithLocals,
                MidenLean.LocalFrame.localAddr]))
      remaining := remaining ++ rem
  return remaining

/-- Close the bridge between the tactic's canonical reflected target and the user goal. -/
private def closeBridgeGoal (goal : MVarId) : TacticM Unit := do
  unless ← goal.isAssigned do
    let _ ←
      try
        runOnGoal goal (← `(tactic|
          first
          | rfl
          | simp [miden_reflect_norm,
                  and_assoc, and_left_comm, and_comm,
                  MidenLean.MidenState.withStack,
                  MidenLean.Symbolic.Expr.eval,
                  MidenLean.Symbolic.Reflect.concreteAssignment,
                  MidenLean.Symbolic.Reflect.concreteState,
                  MidenLean.Symbolic.Reflect.concreteStateWithLocals,
                  MidenLean.LocalFrame.localAddr]
          | apply congrArg some
            ext addr <;>
            simp [miden_reflect_norm,
                  and_assoc, and_left_comm, and_comm,
                  MidenLean.MidenState.withStack,
                  MidenLean.Symbolic.Expr.eval,
                  MidenLean.Symbolic.Reflect.concreteAssignment,
                  MidenLean.Symbolic.Reflect.concreteState,
                  MidenLean.Symbolic.Reflect.concreteStateWithLocals,
                  MidenLean.LocalFrame.localAddr]))
      catch _ =>
        pure [goal]
    pure ()

/-- Return a user-facing rejection reason for instructions outside the
    `miden_reflect` basic-block support boundary. -/
private def unsupportedInstReason? (instExpr : Lean.Expr) : MetaM (Option String) := do
  let instExpr ← whnf instExpr
  match_expr instExpr with
  | MidenLean.Instruction.memLoad =>
      pure <| some "dynamic-address memory instruction `memLoad` is unsupported. \
        Use manual chunking or extend the symbolic executor first."
  | MidenLean.Instruction.memStore =>
      pure <| some "dynamic-address memory instruction `memStore` is unsupported. \
        Use manual chunking or extend the symbolic executor first."
  | MidenLean.Instruction.memLoadwBe =>
      pure <| some "dynamic-address memory instruction `memLoadwBe` is unsupported. \
        Use manual chunking or extend the symbolic executor first."
  | MidenLean.Instruction.memStorewBe =>
      pure <| some "dynamic-address memory instruction `memStorewBe` is unsupported. \
        Use manual chunking or extend the symbolic executor first."
  | MidenLean.Instruction.memLoadwLe =>
      pure <| some "dynamic-address memory instruction `memLoadwLe` is unsupported. \
        Use manual chunking or extend the symbolic executor first."
  | MidenLean.Instruction.memStorewLe =>
      pure <| some "dynamic-address memory instruction `memStorewLe` is unsupported. \
        Use manual chunking or extend the symbolic executor first."
  | _ => pure none

/-- Return a user-facing rejection reason for ops outside the current
    `miden_reflect` support boundary. -/
private def unsupportedOpReason? (opExpr : Lean.Expr) : MetaM (Option String) := do
  let opExpr ← whnf opExpr
  match_expr opExpr with
  | MidenLean.Op.inst inst =>
      unsupportedInstReason? inst
  | MidenLean.Op.ifElse _ _ =>
      pure <| some "control-flow op `ifElse` is unsupported. Use `miden_vcg` or manual chunking."
  | MidenLean.Op.repeat _ _ =>
      pure <| some "control-flow op `repeat` is unsupported. Use `miden_vcg` or manual chunking."
  | MidenLean.Op.whileTrue _ =>
      pure <| some "control-flow op `whileTrue` is unsupported. Use `miden_vcg` or manual chunking."
  | _ => pure none

/-- If a direct `.exec` target definitely reduces to `none` in the concrete
    environment, return that target for a user-facing error. -/
private def firstMissingConcreteCall?
    (envExpr : Lean.Expr) (opExprs : Array Lean.Expr) : MetaM (Option Lean.Expr) := do
  for i in [:opExprs.size] do
    if let some targetExpr ← execTargetExpr? opExprs[i]! then
      let reduced ← whnf (Lean.mkApp envExpr targetExpr)
      if reduced.isAppOfArity ``Option.none 1 then
        return some targetExpr
  return none

/-- Parse the current goal as a supported `exec` / `execWithEnv` equation. -/
private def parseReflectGoal : TacticM ReflectGoal := do
  let mvarId ← getMainGoal
  let goal ← mvarId.getType
  let some (_, lhs0, _) := goal.eq?
    | throwError "miden_reflect: goal is not an equation"

  let isExec := lhs0.isAppOf ``MidenLean.exec && lhs0.getAppNumArgs == 3
  let isExecWithEnv := lhs0.isAppOf ``MidenLean.execWithEnv && lhs0.getAppNumArgs == 4
  unless isExec || isExecWithEnv do
    throwError "miden_reflect: LHS should be `MidenLean.exec fuel state proc` or \
      `MidenLean.execWithEnv env fuel state proc`"

  if isExec then
    evalTactic (← `(tactic| unfold MidenLean.exec))

  let mvarId ← getMainGoal
  let goal ← mvarId.getType
  let some (_, lhs, rhs) := goal.eq?
    | throwError "miden_reflect: goal is not an equation after unfolding"

  unless lhs.isAppOf ``MidenLean.execWithEnv && lhs.getAppNumArgs == 4 do
    throwError "miden_reflect: LHS should be `MidenLean.execWithEnv env fuel state proc`"

  let envExpr := lhs.getArg! 0
  let fuelExpr := lhs.getArg! 1
  let stateExpr := lhs.getArg! 2
  let procExpr := lhs.getArg! 3

  let stateWhnf ← whnf stateExpr
  let (stackExpr, memExpr, framesExpr, advExpr, stackElems, restExpr, useStateWrapper) ←
    if stateWhnf.getAppNumArgs == 4 then
      let stackExpr := stateWhnf.getArg! 0
      let memExpr := stateWhnf.getArg! 1
      let framesExpr := stateWhnf.getArg! 2
      let advExpr := stateWhnf.getArg! 3
      let (stackElems, restExpr) ← extractCons stackExpr
      pure (stackExpr, memExpr, framesExpr, advExpr, stackElems, restExpr, false)
    else
      let stackExpr := Lean.mkProj ``MidenLean.MidenState 0 stateExpr
      let memExpr := Lean.mkProj ``MidenLean.MidenState 1 stateExpr
      let framesExpr := Lean.mkProj ``MidenLean.MidenState 2 stateExpr
      let advExpr := Lean.mkProj ``MidenLean.MidenState 3 stateExpr
      let (stackElems, restExpr) ← findStackDecomposition stateExpr
      pure (stackExpr, memExpr, framesExpr, advExpr, stackElems, restExpr, true)

  let procWhnf ← whnf procExpr
  unless procWhnf.getAppNumArgs == 3 do
    throwError "miden_reflect: could not reduce procedure to ⟨name, numLocals, body⟩"
  let bodyExpr := procWhnf.getArg! 2
  let some opExprs ← extractOps bodyExpr
    | throwError "miden_reflect: could not reduce procedure body to a concrete op list"
  let mut hasExec := false
  for i in [:opExprs.size] do
    if let some reason ← unsupportedOpReason? opExprs[i]! then
      let fmt ← Meta.ppExpr opExprs[i]!
      throwError "miden_reflect: op {fmt} at position {i} is outside the supported \
        straight-line fragment: {reason}"
    if ← opHasExec opExprs[i]! then
      hasExec := true

  pure {
    lhs, rhs, envExpr, fuelExpr, stateExpr, procExpr,
    stackExpr, memExpr, framesExpr, advExpr,
    stackElems, restExpr,
    bodyExpr, opExprs, hasExec, useStateWrapper
  }

/-- Build the wrapper theorem application used by `miden_reflect`. -/
private def buildReflectTheoremExpr
    (goal : ReflectGoal) (gammaExpr? : Option Lean.Expr) : TacticM Lean.Expr := do
  let stackPrefixExpr ← mkListExpr (Lean.mkConst ``MidenLean.Felt) goal.stackElems.toList
  let resultExpr ← mkFreshExprMVar (Lean.mkConst ``MidenLean.Symbolic.BlockResult)
  match gammaExpr?, goal.useStateWrapper with
  | some gammaExpr, true =>
      pure <| Lean.mkAppN
        (Lean.mkConst ``MidenLean.Symbolic.Reflect.reflect_proc_state_using)
        #[goal.procExpr, goal.envExpr, goal.fuelExpr, gammaExpr,
          goal.stateExpr, stackPrefixExpr, goal.restExpr, resultExpr]
  | some gammaExpr, false =>
      pure <| Lean.mkAppN
        (Lean.mkConst ``MidenLean.Symbolic.Reflect.reflect_proc_stack_using)
        #[goal.procExpr, goal.envExpr, goal.fuelExpr, gammaExpr,
          goal.stackExpr, stackPrefixExpr, goal.restExpr,
          goal.memExpr, goal.framesExpr, goal.advExpr, resultExpr]
  | none, true =>
      pure <| Lean.mkAppN
        (Lean.mkConst ``MidenLean.Symbolic.Reflect.reflect_proc_state)
        #[goal.procExpr, goal.envExpr, goal.fuelExpr,
          goal.stateExpr, stackPrefixExpr, goal.restExpr, resultExpr]
  | none, false =>
      pure <| Lean.mkAppN
        (Lean.mkConst ``MidenLean.Symbolic.Reflect.reflect_proc_stack)
        #[goal.procExpr, goal.envExpr, goal.fuelExpr,
          goal.stackExpr, stackPrefixExpr, goal.restExpr,
          goal.memExpr, goal.framesExpr, goal.advExpr, resultExpr]

syntax "miden_reflect" (" using " term)? : tactic

elab_rules : tactic
  | `(tactic| miden_reflect $[using $gammaTerm]?) => do
  let gammaExpr? ← match gammaTerm with
    | some stx => some <$> Lean.Elab.Term.elabTerm stx none
    | none => pure none
  let reflectGoal ← parseReflectGoal
  let gammaExpr? ←
    if let some gammaExpr := gammaExpr? then
      pure (some gammaExpr)
    else if reflectGoal.hasExec then
      if let some targetExpr ← firstMissingConcreteCall? reflectGoal.envExpr reflectGoal.opExprs then
        let fmt ← Meta.ppExpr targetExpr
        throwError "miden_reflect: `.exec` target {fmt} is missing from the concrete `ProcEnv`. \
          Use `execWithEnv` with a reducible environment or pass `using Γ`."
      let minFuelExpr := Lean.mkAppN (Lean.mkConst ``Nat.sub) #[reflectGoal.fuelExpr, Lean.mkNatLit 1]
      pure <| some <|
        Lean.mkAppN (Lean.mkConst ``MidenLean.Symbolic.Reflect.ReflectEnv.ofConcrete)
          #[reflectGoal.envExpr, minFuelExpr]
    else
      pure none
  let mainGoal ← getMainGoal
  let theoremExpr ← buildReflectTheoremExpr reflectGoal gammaExpr?

  -- Insert a canonical middle term before theorem application.
  let targetTy ← inferType reflectGoal.lhs
  let middleExpr ← mkFreshExprMVar targetTy
  let eqTransExpr ← mkAppOptM ``Eq.trans
    #[some targetTy, some reflectGoal.lhs, some middleExpr, some reflectGoal.rhs]
  let goals ←
    try
      mainGoal.apply eqTransExpr
    catch _ =>
      throwError "miden_reflect: failed to insert canonical target"
  let mut eqGoals : List MVarId := []
  let mut auxGoals : List MVarId := []
  for goal in goals do
    unless ← goal.isAssigned do
      let ty ← goal.getType
      if ty.eq?.isSome then
        eqGoals := eqGoals ++ [goal]
      else
        auxGoals := auxGoals ++ [goal]
  let [firstGoal, bridgeGoal] := eqGoals
    | throwError "miden_reflect: expected exactly two equality goals after canonicalization"

  let theoremGoals ←
    try
      firstGoal.apply theoremExpr
    catch _ =>
      throwError "miden_reflect: failed to apply reflection wrapper"
  let mut hstackGoal? : Option MVarId := none
  let mut hfuelGoal? : Option MVarId := none
  let mut hresultGoal? : Option MVarId := none
  let mut hprecondsGoal? : Option MVarId := none
  let mut auxTheoremGoals : List MVarId := []
  for goal in theoremGoals do
    unless ← goal.isAssigned do
      let ty ← goal.getType
      if ← isProp ty then
        match ty.eq? with
        | some (_, lhs, rhs) =>
          if (← hasListTypeOf lhs ``MidenLean.Felt) || (← hasListTypeOf rhs ``MidenLean.Felt) then
            hstackGoal? := some goal
          else if lhs.isAppOf ``MidenLean.Symbolic.Reflect.execProcedure
              || rhs.isAppOf ``MidenLean.Symbolic.Reflect.execProcedure then
            hresultGoal? := some goal
          else
            auxTheoremGoals := auxTheoremGoals ++ [goal]
        | none =>
          if ty.isForall then
            hprecondsGoal? := some goal
          else
            hfuelGoal? := some goal
      else
        auxTheoremGoals := auxTheoremGoals ++ [goal]
  let some hfuelGoal := hfuelGoal? | throwError "miden_reflect: missing `hfuel` goal"
  let some hresultGoal := hresultGoal? | throwError "miden_reflect: missing `hresult` goal"
  let some hprecondsGoal := hprecondsGoal? | throwError "miden_reflect: missing `hpreconds` goal"

  if let some hstackGoal := hstackGoal? then
    closeGoalWith hstackGoal "`hstack`" (← `(tactic|
      first
      | assumption
      | symm; assumption
      | rfl
      | simp))
  closeGoalWith hfuelGoal "`hfuel`" (← `(tactic| omega))
  closeGoalWith hresultGoal "`hresult`" (← `(tactic|
    first
    | rfl
    | simp [MidenLean.Symbolic.Reflect.execProcedure,
            MidenLean.Symbolic.Reflect.procSpec,
            MidenLean.Symbolic.Reflect.ReflectEnv.ofConcrete,
            MidenLean.Symbolic.Reflect.ReflectEnv.toSymbolic,
            MidenLean.Symbolic.Reflect.ReflectEnv.empty,
            MidenLean.Symbolic.Reflect.concreteState,
            MidenLean.Symbolic.execOps,
            MidenLean.Symbolic.execOp,
            MidenLean.Symbolic.execInstruction,
            bind, Bind.bind, Option.bind]))
  let bridgeRemaining ←
    try
      runOnGoal bridgeGoal (← `(tactic|
        first
        | rfl
        | simp [miden_reflect_norm,
                and_assoc, and_left_comm, and_comm,
                MidenLean.MidenState.withStack,
                MidenLean.Symbolic.Expr.eval,
                MidenLean.Symbolic.Reflect.concreteAssignment,
                MidenLean.Symbolic.Reflect.concreteState,
                MidenLean.Symbolic.Reflect.concreteStateWithLocals,
                MidenLean.LocalFrame.localAddr]
        | apply congrArg some
          ext addr <;>
          simp [miden_reflect_norm,
                and_assoc, and_left_comm, and_comm,
                MidenLean.MidenState.withStack,
                MidenLean.Symbolic.Expr.eval,
                MidenLean.Symbolic.Reflect.concreteAssignment,
                MidenLean.Symbolic.Reflect.concreteState,
                MidenLean.Symbolic.Reflect.concreteStateWithLocals,
                MidenLean.LocalFrame.localAddr]))
    catch _ =>
      pure [bridgeGoal]

  let mut remainingSeeds := [hprecondsGoal]
  remainingSeeds := remainingSeeds ++ bridgeRemaining
  for goal in auxTheoremGoals do
    unless ← goal.isAssigned do
      remainingSeeds := remainingSeeds ++ [goal]
  for goal in auxGoals do
    unless ← goal.isAssigned do
      remainingSeeds := remainingSeeds ++ [goal]
  let remaining ← cleanupGoals remainingSeeds
  setGoals remaining
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing

end MidenLean.Symbolic.Tactic

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
