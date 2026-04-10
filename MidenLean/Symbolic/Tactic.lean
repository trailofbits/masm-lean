import MidenLean.Symbolic.Reflect
import MidenLean.Proofs.ControlFlow
import MidenLean.Proofs.Tactics

/-!
# Proof Automation Tactics

## `miden_reflect`

Automates reflection for straight-line procedure proofs.
Supported goals are `execProcedure emptyEnv` / `execProcedure` equations whose procedure body is a
straight-line `List Op`. Control flow is still rejected. Procedures with
`.exec` calls are supported through `miden_reflect using Γ`, where `Γ` is a
`ReflectEnv` carrying symbolic callee summaries and soundness proofs.

Given a goal `execProcedure emptyEnv fuel ⟨stack, mem, frames, adv⟩ proc = some ⟨result, ...⟩`
or `execProcedure env fuel ⟨stack, mem, frames, adv⟩ proc = some ⟨result, ...⟩`,
the tactic:
1. Extracts the instruction list from `proc.body`
2. Canonicalizes the target to the wrapper-theorem surface
3. Applies `reflect_with_env_zero` or `reflect_with_env_locals`
4. Closes mechanical setup goals automatically
5. Leaves semantic precondition obligations for the user, if any

## `miden_vcg`

Decomposes control flow in `execProcedure`-based existential goals.
Scans the procedure's `List Op` for control-flow ops and applies
the appropriate composition rule:
- **`Op.ifElse`**: applies `execProcedure_ifElse`, generating branch subgoals
- **`Op.repeat`**: applies `execProcedure_repeat`, generating invariant subgoals
- **`Op.whileTrue`**: applies `execProcedure_while`, generating invariant/measure subgoals

For mixed op lists (prefix instructions + control flow), the tactic splits
at the first control-flow boundary using `execProcedure_append`, reduces the
prefix via `simp`, then applies the composition rule.
-/

namespace MidenLean.Symbolic.Tactic

open Lean Elab Tactic Meta PrettyPrinter

/-- Goal data extracted from an `execProcedure emptyEnv` / `execProcedure` equation. -/
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

/-- Goal data extracted from an `execProcedure emptyEnv` / `execProcedure` equation without
    imposing the straight-line restriction used by `miden_reflect`. -/
private structure ExecGoal where
  lhs : Lean.Expr
  rhs : Lean.Expr
  envExpr : Lean.Expr
  fuelExpr : Lean.Expr
  stateExpr : Lean.Expr
  procExpr : Lean.Expr
  bodyExpr : Lean.Expr
  numLocalsExpr : Lean.Expr
  opExprs : Array Lean.Expr

/-- The first control-flow boundary in an op list. -/
private inductive ControlBoundary where
  | ifElse (thenOps : Lean.Expr) (elseOps : Lean.Expr)
  | repeat (countExpr : Lean.Expr) (bodyOps : Lean.Expr)
  | whileTrue (bodyOps : Lean.Expr)

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

/-- Check whether an op is an `execProcedure emptyEnv` call. -/
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

private def mkOpListExpr (xs : List Lean.Expr) : MetaM Lean.Expr :=
  mkListExpr (Lean.mkConst ``MidenLean.Op) xs

/-- Check if a Lean `Expr` is a `Nat` literal equal to zero. -/
private def isNatZero (e : Lean.Expr) : Bool :=
  e.numeral? == some 0 || e.isConstOf ``Nat.zero

private def isOfOpsProc (e : Lean.Expr) : Bool :=
  e.isAppOfArity ``MidenLean.Procedure.ofOps 1

/-- Check whether an expression has type `List α` for the given element type. -/
private def hasListTypeOf (e : Lean.Expr) (elemTyName : Lean.Name) : MetaM Bool := do
  let ty ← whnf (← inferType e)
  pure <|
    ty.isAppOfArity ``List 1 &&
    (ty.getArg! 0).isConstOf elemTyName

/-- Find a local hypothesis that decomposes `state.stack`. -/
private def findStackDecomposition (stateExpr : Lean.Expr) : TacticM (Array Lean.Expr × Lean.Expr) := do
  let stackProj := Lean.mkProj ``MidenLean.Concrete.State 0 stateExpr
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

/-- If an equality goal has an unassigned metavariable on one side, assign it
    directly to the other side and close the goal by reflexivity. -/
private def closeEqByAssigningMVar? (goal : MVarId) : TacticM Bool := do
  if ← goal.isAssigned then
    return true
  let ty ← goal.getType
  let some (_, lhs, rhs) := ty.eq?
    | return false
  if lhs.isMVar then
    let lhsId := lhs.mvarId!
    unless ← lhsId.isAssigned do
      try
        lhsId.assign rhs
        goal.assign (← mkEqRefl (← instantiateMVars rhs))
        return true
      catch _ =>
        pure ()
  if rhs.isMVar then
    let rhsId := rhs.mvarId!
    unless ← rhsId.isAssigned do
      try
        rhsId.assign lhs
        goal.assign (← mkEqRefl (← instantiateMVars lhs))
        return true
      catch _ =>
        pure ()
  if lhs.isAppOfArity ``Option.some 2 && rhs.isAppOfArity ``Option.some 2 then
    let lhsArg := lhs.getArg! 1
    let rhsArg := rhs.getArg! 1
    if lhsArg.isMVar then
      let lhsId := lhsArg.mvarId!
      unless ← lhsId.isAssigned do
        try
          lhsId.assign rhsArg
          goal.assign (← mkEqRefl (← instantiateMVars rhs))
          return true
        catch _ =>
          pure ()
    if rhsArg.isMVar then
      let rhsId := rhsArg.mvarId!
      unless ← rhsId.isAssigned do
        try
          rhsId.assign lhsArg
          goal.assign (← mkEqRefl (← instantiateMVars lhs))
          return true
        catch _ =>
          pure ()
  return false

private def closeReflectResultGoal (goal : MVarId) : TacticM Unit := do
  unless ← goal.isAssigned do
    let tryReduce : TacticM Bool := do
      let ty ← goal.getType
      let some (_, lhs, rhs) := ty.eq?
        | return false
      let lhs' ← withTransparency TransparencyMode.all <| reduce lhs
      let rhs' ← withTransparency TransparencyMode.all <| reduce rhs
      if lhs'.isAppOfArity ``Option.some 2 && rhs'.isAppOfArity ``Option.some 2 then
        let lhsArg := lhs'.getArg! 1
        let rhsArg := rhs'.getArg! 1
        if rhsArg.isMVar then
          let rhsId := rhsArg.mvarId!
          unless ← rhsId.isAssigned do
            try
              rhsId.assign lhsArg
              goal.assign (← mkEqRefl (← instantiateMVars lhs'))
              return true
            catch _ =>
              pure ()
        if lhsArg.isMVar then
          let lhsId := lhsArg.mvarId!
          unless ← lhsId.isAssigned do
            try
              lhsId.assign rhsArg
              goal.assign (← mkEqRefl (← instantiateMVars rhs'))
              return true
            catch _ =>
              pure ()
      if ← isDefEq lhs' rhs' then
        goal.assign (← mkEqRefl (← instantiateMVars lhs'))
        return true
      return false
    if ← tryReduce then
      pure ()
    else
    let remaining ← runOnGoal goal (← `(tactic|
      simp [MidenLean.Symbolic.Reflect.execProcedure,
            MidenLean.Symbolic.Reflect.procSpec,
            MidenLean.Symbolic.Reflect.ReflectEnv.empty,
            MidenLean.Symbolic.Reflect.concreteState,
            MidenLean.Symbolic.execOps,
            MidenLean.Symbolic.execOp,
            MidenLean.Symbolic.execInstruction,
            bind, Bind.bind, Option.bind]))
    match remaining with
    | [] => pure ()
    | [goal'] =>
        unless ← closeEqByAssigningMVar? goal' do
          closeGoalWith goal' "`hresult`" (← `(tactic| rfl))
    | goal' :: _ =>
        let ty ← goal'.getType
        throwError "miden_reflect: failed to solve `hresult`:{indentExpr ty}"

/-- Apply light cleanup to remaining goals, closing trivial `hpreconds` goals. -/
private def cleanupGoals (goals : List MVarId) : TacticM (List MVarId) := do
  let mut remaining : List MVarId := []
  for goal in goals do
    unless ← goal.isAssigned do
      let rem ← runOnGoal goal (← `(tactic|
        try
          simp [miden_reflect_norm,
                and_assoc, and_left_comm, and_comm,
                MidenLean.Concrete.State.withStack,
                MidenLean.Symbolic.Precondition.holds,
                MidenLean.Symbolic.Expr.eval,
                MidenLean.Symbolic.Reflect.concreteAssignment,
                MidenLean.Symbolic.Reflect.concreteState,
                MidenLean.Symbolic.Reflect.concreteStateWithLocals,
                MidenLean.LocalFrame.localAddr]))
      remaining := remaining ++ rem
  return remaining

/-- Simplify the bridge between the tactic's canonical reflected target and the
    user goal, directly instantiating state metavariables when possible. -/
private def closeBridgeGoal (goal : MVarId) : TacticM (List MVarId) := do
  if ← goal.isAssigned then
    pure []
  else
    let remaining ←
      try
        runOnGoal goal (← `(tactic|
          first
          | simp [miden_reflect_norm,
                  and_assoc, and_left_comm, and_comm,
                  MidenLean.Concrete.State.withStack,
                  MidenLean.Symbolic.Expr.eval,
                  MidenLean.Symbolic.Reflect.concreteAssignment,
                  MidenLean.Symbolic.Reflect.concreteState,
                  MidenLean.Symbolic.Reflect.concreteStateWithLocals,
                  MidenLean.LocalFrame.localAddr]
          | apply congrArg some
          | rfl
          | ext addr <;>
            simp [miden_reflect_norm,
                  and_assoc, and_left_comm, and_comm,
                  MidenLean.Concrete.State.withStack,
                  MidenLean.Symbolic.Expr.eval,
                  MidenLean.Symbolic.Reflect.concreteAssignment,
                  MidenLean.Symbolic.Reflect.concreteState,
                  MidenLean.Symbolic.Reflect.concreteStateWithLocals,
                  MidenLean.LocalFrame.localAddr]))
      catch _ =>
        pure [goal]
    let mut unresolved : List MVarId := []
    for remGoal in remaining do
      unless ← remGoal.isAssigned do
        unless ← closeEqByAssigningMVar? remGoal do
          unresolved := unresolved ++ [remGoal]
    pure unresolved

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

private def lastNameComponent? : Lean.Name → Option String
  | .str _ s => some s
  | _ => none

private def stringLitExpr? (e : Lean.Expr) : MetaM (Option String) := do
  let e ← whnf e
  match e with
  | .lit (.strVal s) => pure (some s)
  | _ => pure none

/-- Infer a convention-based theorem-backed execution summary name from the
    concrete procedure environment and direct `.exec` target. For example,
    `u128ProcEnv` plus `"wrapping_mul"` maps to
    `MidenLean.Proofs.u128_wrapping_mul_exec`. -/
private def execOverrideTheoremName?
    (envExpr targetExpr : Lean.Expr) : MetaM (Option Lean.Name) := do
  let some envConst := envExpr.getAppFn.constName? | return none
  let some envBase := lastNameComponent? envConst | return none
  if !envBase.endsWith "ProcEnv" then
    return none
  let some target := ← stringLitExpr? targetExpr | return none
  let stem := envBase.dropEnd "ProcEnv".length
  let theoremName := Lean.Name.str envConst.getPrefix s!"{stem}_{target}_exec"
  try
    let _ ← getConstInfo theoremName
    return some theoremName
  catch _ =>
    return none

/-- Reduce `env target` to the concrete callee procedure, when the environment
    is sufficiently reducible for theorem-backed call summaries. -/
private def concreteCalleeExpr?
    (envExpr targetExpr : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let reduced ← whnf (Lean.mkApp envExpr targetExpr)
  match_expr reduced with
  | Option.some callee => pure (some callee)
  | _ => pure none

/-- Normalize goal (no-op: all goals are already `execProcedure` form). -/
private def normalizeExecGoal (goal : MVarId) : TacticM MVarId :=
  pure goal

/-- Parse the current goal as an `execProcedure` equation with a concrete op list. -/
private def parseExecGoal (goal : MVarId) : TacticM ExecGoal := do
  let goal ← normalizeExecGoal goal
  let goalTy ← goal.getType
  let some (_, lhs, rhs) := goalTy.eq?
    | throwError "miden_vcg: goal is not an equation"

  unless lhs.isAppOf ``MidenLean.execProcedure && lhs.getAppNumArgs == 4 do
    throwError "miden_vcg: goal must be `execProcedure emptyEnv` or `execProcedure`"

  let envExpr := lhs.getArg! 0
  let fuelExpr := lhs.getArg! 1
  let stateExpr := lhs.getArg! 2
  let procExpr := lhs.getArg! 3
  let procWhnf ← whnf procExpr
  unless procWhnf.getAppNumArgs == 3 do
    throwError "miden_vcg: could not reduce procedure to ⟨name, numLocals, body⟩"
  let numLocalsExpr := procWhnf.getArg! 1
  let bodyExpr := procWhnf.getArg! 2
  let some opExprs ← extractOps bodyExpr
    | throwError "miden_vcg: could not reduce procedure body to a concrete op list"

  pure {
    lhs, rhs, envExpr, fuelExpr, stateExpr, procExpr,
    bodyExpr, numLocalsExpr, opExprs
  }

private def controlBoundary? (opExpr : Lean.Expr) : MetaM (Option ControlBoundary) := do
  let opExpr ← whnf opExpr
  match_expr opExpr with
  | MidenLean.Op.ifElse thenOps elseOps =>
      pure <| some (.ifElse thenOps elseOps)
  | MidenLean.Op.repeat count body =>
      pure <| some (.repeat count body)
  | MidenLean.Op.whileTrue body =>
      pure <| some (.whileTrue body)
  | _ =>
      pure none

private def firstControlBoundary?
    (opExprs : Array Lean.Expr) : MetaM (Option (Nat × ControlBoundary)) := do
  for i in [:opExprs.size] do
    if let some boundary ← controlBoundary? opExprs[i]! then
      return some (i, boundary)
  return none

private def branchBodyMatches (goal : MVarId) (opsExpr : Lean.Expr) : TacticM Bool := do
  let parsed ← parseExecGoal goal
  isDefEq parsed.bodyExpr opsExpr

private def firstExecSplitIndex? (opExprs : Array Lean.Expr) : MetaM (Option Nat) := do
  if opExprs.size ≤ 1 then
    return none
  for i in [:opExprs.size] do
    if ← opHasExec opExprs[i]! then
      return some (if i = 0 then 1 else i)
  return none

private def rewriteZeroLocalsGoalToBody (goal : MVarId) : TacticM MVarId := do
  let goal ← normalizeExecGoal goal
  let parsed ← parseExecGoal goal
  if isOfOpsProc parsed.procExpr then
    pure goal
  else
    unless isNatZero parsed.numLocalsExpr do
      throwError "miden_vcg: control-flow procedures with `numLocals > 0` are not yet supported"
    let hbodyType ← mkEq (Lean.mkProj ``MidenLean.Procedure 2 parsed.procExpr) parsed.bodyExpr
    let hlocalsType ← mkEq (Lean.mkProj ``MidenLean.Procedure 1 parsed.procExpr) (Lean.mkNatLit 0)
    let hbody ← mkFreshExprMVar hbodyType
    let hlocals ← mkFreshExprMVar hlocalsType
    let closeProjectionGoal (goal : MVarId) (label : String) : TacticM Unit := do
      if let some procName := parsed.procExpr.getAppFn.constName? then
        let procIdent := mkIdent procName
        closeGoalWith goal label (← `(tactic|
          first
          | rfl
          | delta $procIdent; rfl
          | simp))
      else
        closeGoalWith goal label (← `(tactic|
          first
          | rfl
          | simp))
    closeProjectionGoal hbody.mvarId! "`hbody`"
    closeProjectionGoal hlocals.mvarId! "`hlocals`"
    let theoremExpr := Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure_body_eq)
      #[parsed.envExpr, parsed.fuelExpr, parsed.stateExpr,
        parsed.procExpr, parsed.bodyExpr, hbody, hlocals]
    try
      let rwResult ← goal.rewrite (← goal.getType) theoremExpr
      let goal' ← goal.replaceTargetEq rwResult.eNew rwResult.eqProof
      pure goal'
    catch ex =>
      let procFmt ← Meta.ppExpr parsed.procExpr
      let bodyFmt ← Meta.ppExpr parsed.bodyExpr
      throwError "miden_vcg: failed to rewrite goal to procedure body for {procFmt} with body {bodyFmt}: {ex.toMessageData}"

private def rewriteGoalToOfOpsBody (goal : MVarId) (bodyExpr : Lean.Expr) : TacticM MVarId := do
  let goal ← normalizeExecGoal goal
  let parsed ← parseExecGoal goal
  let procExpr := Lean.mkApp (Lean.mkConst ``MidenLean.Procedure.ofOps) bodyExpr
  let targetNew ← mkEq
    (Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure)
      #[parsed.envExpr, parsed.fuelExpr, parsed.stateExpr, procExpr])
    parsed.rhs
  goal.replaceTargetDefEq targetNew

private def rewriteGoalToOfOpsAppend
    (goal : MVarId) (prefixExpr suffixExpr : Lean.Expr) : TacticM MVarId := do
  let bodyExpr ← mkAppM ``List.append #[prefixExpr, suffixExpr]
  rewriteGoalToOfOpsBody goal bodyExpr

/-- Parse the current goal as an `execProcedure` equation. -/
private def parseReflectGoal : TacticM ReflectGoal := do
  let mvarId ← getMainGoal
  let goal ← mvarId.getType
  let some (_, lhs, rhs) := goal.eq?
    | throwError "miden_reflect: goal is not an equation"

  unless lhs.isAppOf ``MidenLean.execProcedure && lhs.getAppNumArgs == 4 do
    throwError "miden_reflect: LHS should be `MidenLean.execProcedure env fuel state proc`"

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
      let stackExpr := Lean.mkProj ``MidenLean.Concrete.State 0 stateExpr
      let memExpr := Lean.mkProj ``MidenLean.Concrete.State 1 stateExpr
      let framesExpr := Lean.mkProj ``MidenLean.Concrete.State 2 stateExpr
      let advExpr := Lean.mkProj ``MidenLean.Concrete.State 3 stateExpr
      let stackProjWhnf ← whnf stackExpr
      let (stackElems, restExpr) ←
        if stateExpr.isAppOfArity ``MidenLean.Concrete.State.withStack 2 ||
            stackProjWhnf.isAppOfArity ``List.nil 1 ||
            stackProjWhnf.isAppOfArity ``List.cons 2 then
          extractCons stackExpr
        else
          findStackDecomposition stateExpr
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

/-- Try to close a singleton `.exec` goal by rewriting it to a direct callee
    execution goal and applying a convention-based `*_exec` theorem. This is
    the preferred path for large callee leaves, with symbolic reflection kept as
    the fallback. -/
private def tryExecOverrideTheorem? (goal : MVarId) : TacticM (Option (List MVarId)) := do
  let goal ← normalizeExecGoal goal
  let parsed0 ← parseExecGoal goal
  if !isNatZero parsed0.numLocalsExpr then
    return none
  let goal ← rewriteZeroLocalsGoalToBody goal
  let parsed ← parseExecGoal goal
  if parsed.opExprs.size != 1 then
    return none
  let some targetExpr ← execTargetExpr? parsed.opExprs[0]! | return none
  let some theoremName ← execOverrideTheoremName? parsed.envExpr targetExpr | return none
  let some calleeExpr ← concreteCalleeExpr? parsed.envExpr targetExpr | return none

  let directFuelExpr ← mkFreshExprMVar (Lean.mkConst ``Nat)
  let directCallExpr := Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure)
    #[parsed.envExpr, directFuelExpr, parsed.stateExpr, calleeExpr]
  let targetTy ← inferType parsed.lhs
  let eqTransExpr ← mkAppOptM ``Eq.trans
    #[some targetTy, some parsed.lhs, some directCallExpr, some parsed.rhs]
  let splitGoals ←
    try
      goal.apply eqTransExpr
    catch ex =>
      throwError "miden_reflect: failed to insert theorem-backed singleton-call target `{theoremName}`: {ex.toMessageData}"
  let mut eqGoals : List MVarId := []
  let mut auxGoals : List MVarId := []
  for g in splitGoals do
    unless ← g.isAssigned do
      let ty ← g.getType
      if ty.eq?.isSome then
        eqGoals := eqGoals ++ [g]
      else
        auxGoals := auxGoals ++ [g]
  let [bridgeGoal, callGoal] := eqGoals
    | throwError "miden_reflect: expected two equality goals for theorem-backed singleton-call summary `{theoremName}`"

  let someCalleeExpr ← mkAppM ``Option.some #[calleeExpr]
  let hlookupType ← mkEq (Lean.mkApp parsed.envExpr targetExpr) someCalleeExpr
  let hlookupExpr ← mkFreshExprMVar hlookupType
  let bridgeGoals ←
    try
      bridgeGoal.apply (Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure_singleton_exec_eq)
        #[parsed.envExpr, directFuelExpr, parsed.stateExpr, targetExpr, calleeExpr, hlookupExpr])
    catch ex =>
      throwError "miden_reflect: failed to prove theorem-backed singleton-call bridge `{theoremName}`: {ex.toMessageData}"
  let mut bridgeRemaining : List MVarId := []
  for g in bridgeGoals do
    unless ← g.isAssigned do
      let rem ←
        runOnGoal g (← `(tactic|
          first
          | assumption
          | symm; assumption
          | rfl
          | simp))
      bridgeRemaining := bridgeRemaining ++ rem

  let theoremGoals ←
    try
      callGoal.apply (Lean.mkConst theoremName)
    catch ex =>
      throwError "miden_reflect: theorem-backed summary `{theoremName}` did not match the direct callee goal: {ex.toMessageData}"
  let mut remaining : List MVarId := []
  for g in theoremGoals ++ bridgeRemaining ++ auxGoals do
    unless ← g.isAssigned do
      let rem ←
        runOnGoal g (← `(tactic|
          first
          | assumption
          | symm; assumption
          | rfl
          | simp [MidenLean.Concrete.State.withStack]))
      remaining := remaining ++ rem
  pure (some remaining)

syntax "miden_reflect" (" using " term)? : tactic

elab_rules : tactic
  | `(tactic| miden_reflect $[using $gammaTerm]?) => do
  let gammaExpr? ← match gammaTerm with
    | some stx => some <$> Lean.Elab.Term.elabTerm stx none
    | none => pure none
  let reflectGoal ← parseReflectGoal
  let mainGoal ← getMainGoal
  if let some remaining ← tryExecOverrideTheorem? mainGoal then
    setGoals remaining
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    return
  let gammaExpr? ←
    if let some gammaExpr := gammaExpr? then
      pure (some gammaExpr)
    else if reflectGoal.hasExec then
      if let some targetExpr ← firstMissingConcreteCall? reflectGoal.envExpr reflectGoal.opExprs then
        let fmt ← Meta.ppExpr targetExpr
        throwError "miden_reflect: `.exec` target {fmt} is missing from the concrete `ProcEnv`. \
          Use `execProcedure` with a reducible environment or pass `using Γ`."
      let minFuelExpr := Lean.mkAppN (Lean.mkConst ``Nat.sub) #[reflectGoal.fuelExpr, Lean.mkNatLit 1]
      pure <| some <|
        Lean.mkAppN (Lean.mkConst ``MidenLean.Symbolic.Reflect.ReflectEnv.ofConcrete)
          #[reflectGoal.envExpr, minFuelExpr]
    else
      pure none
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
  closeReflectResultGoal hresultGoal
  let bridgeRemaining ← closeBridgeGoal bridgeGoal

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

private def closeVcgStackGoal (goal : MVarId) : TacticM Unit := do
  closeGoalWith goal "`hs`" (← `(tactic|
    first
    | assumption
    | symm; assumption
    | rfl
    | simp [MidenLean.Concrete.State.withStack]))

private def closeVcgFuelGoal (goal : MVarId) : TacticM Unit := do
  closeGoalWith goal "`hfuel`" (← `(tactic| omega))

private def closeVcgBoolGoal (goal : MVarId) : TacticM (List MVarId) := do
  runOnGoal goal (← `(tactic|
    first
    | assumption
    | simp [miden_reflect_norm,
            MidenLean.Concrete.State.withStack,
            MidenLean.LocalFrame.localAddr,
            and_assoc, and_left_comm, and_comm]
    | tauto
    | omega))

private def canonicalizeVcgGoal
    (goal : MVarId) (closeBridges : Bool := true) : TacticM (MVarId × List MVarId) := do
  let goal ← normalizeExecGoal goal
  let goalTy ← goal.getType
  let some (_, lhs, rhs) := goalTy.eq?
    | pure (goal, [])
  if rhs.isMVar || rhs.isAppOfArity ``Option.some 2 then
    pure (goal, [])
  else
    let targetTy ← inferType lhs
    let stateExpr ← mkFreshExprMVar (Lean.mkConst ``MidenLean.Concrete.State)
    let middleExpr ← mkAppM ``Option.some #[stateExpr]
    let eqTransExpr ← mkAppOptM ``Eq.trans
      #[some targetTy, some lhs, some middleExpr, some rhs]
    let goals ←
      try
        goal.apply eqTransExpr
      catch _ =>
        throwError "miden_vcg: failed to insert canonical target"
    let mut execGoal? : Option MVarId := none
    let mut bridgeSeeds : List MVarId := []
    for g in goals do
      unless ← g.isAssigned do
        let ty ← g.getType
        match ty.eq? with
        | some (_, glhs, _) =>
            if glhs.isAppOf ``MidenLean.execProcedure then
              execGoal? := some g
            else
              bridgeSeeds := bridgeSeeds ++ [g]
        | none =>
            bridgeSeeds := bridgeSeeds ++ [g]
    let some execGoal := execGoal?
      | throwError "miden_vcg: canonicalization did not produce an execution goal"
    if closeBridges then
      let mut bridgeRemaining : List MVarId := []
      for g in bridgeSeeds do
        unless ← g.isAssigned do
          bridgeRemaining := bridgeRemaining ++ (← closeBridgeGoal g)
      pure (execGoal, bridgeRemaining)
    else
      pure (execGoal, bridgeSeeds)

mutual

private partial def decomposeAppendGoalAt (goal : MVarId) (splitAt : Nat) : TacticM (List MVarId) := do
  let goal ← normalizeExecGoal goal
  let parsed0 ← parseExecGoal goal
  if !isNatZero parsed0.numLocalsExpr then
    throwError "miden_vcg: control-flow procedures with `numLocals > 0` are not yet supported"
  let goal ← rewriteZeroLocalsGoalToBody goal
  let parsed1 ← parseExecGoal goal
  let prefixExpr ← mkOpListExpr (parsed1.opExprs.toList.take splitAt)
  let suffixExpr ← mkOpListExpr (parsed1.opExprs.toList.drop splitAt)
  let goal ← rewriteGoalToOfOpsAppend goal prefixExpr suffixExpr
  let (goal, bridgeSeeds) ← canonicalizeVcgGoal goal
  let parsed ← parseExecGoal goal
  let midStateExpr ← mkFreshExprMVar (Lean.mkConst ``MidenLean.Concrete.State)
  let finalStateExpr ← mkFreshExprMVar (Lean.mkConst ``MidenLean.Concrete.State)
  let theoremExpr := Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure_append_eq)
    #[parsed.envExpr, parsed.fuelExpr, parsed.stateExpr,
      prefixExpr, suffixExpr, midStateExpr, finalStateExpr]
  let goals ←
    try
      goal.apply theoremExpr
    catch ex =>
      let procFmt ← Meta.ppExpr parsed.procExpr
      throwError "miden_vcg: failed to apply append decomposition for {procFmt}: {ex.toMessageData}"
  let mut execGoals : List MVarId := []
  let mut auxGoals : List MVarId := []
  for g in goals do
    unless ← g.isAssigned do
      let ty ← g.getType
      if ty.eq?.isSome then
        execGoals := execGoals ++ [g]
      else
        auxGoals := auxGoals ++ [g]
  let [execGoal1, execGoal2] := execGoals
    | do
        let goalTypes ← goals.mapM (fun g => do
          let fmt ← Meta.ppExpr (← g.getType)
          pure <| MessageData.ofFormat fmt)
        let joined := MessageData.joinSep goalTypes " | "
        throwError "miden_vcg: append decomposition returned {goals.length} goals: {joined}"
  let goal1IsPrefix ← branchBodyMatches execGoal1 prefixExpr
  let goal1IsSuffix ← branchBodyMatches execGoal1 suffixExpr
  let goal2IsPrefix ← branchBodyMatches execGoal2 prefixExpr
  let goal2IsSuffix ← branchBodyMatches execGoal2 suffixExpr
  let (prefixGoal, suffixGoal) ←
    if goal1IsPrefix && goal2IsSuffix then
      pure (execGoal1, execGoal2)
    else if goal1IsSuffix && goal2IsPrefix then
      pure (execGoal2, execGoal1)
    else
      throwError "miden_vcg: could not classify append decomposition goals"
  let prefixRemaining ← decomposeVcgGoal prefixGoal
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let suffixRemaining ← decomposeVcgGoal suffixGoal
  let auxRemaining ← cleanupGoals auxGoals
  let bridgeRemaining ← cleanupGoals bridgeSeeds
  return prefixRemaining ++ suffixRemaining ++ auxRemaining ++ bridgeRemaining

private partial def decomposeVcgGoal (goal : MVarId) : TacticM (List MVarId) := do
  if ← goal.isAssigned then
    pure []
  else
    let goal ← normalizeExecGoal goal
    let parsed0 ← parseExecGoal goal
    let noControl := (← firstControlBoundary? parsed0.opExprs).isNone
    if noControl then
      if !isNatZero parsed0.numLocalsExpr then
        return ← runOnGoal goal (← `(tactic| miden_reflect))
      let goal ← rewriteZeroLocalsGoalToBody goal
      let parsed ← parseExecGoal goal
      if let some splitAt ← firstExecSplitIndex? parsed.opExprs then
        return ← decomposeAppendGoalAt goal splitAt
      else
        return ← runOnGoal goal (← `(tactic| miden_reflect))

    if !isNatZero parsed0.numLocalsExpr then
      throwError "miden_vcg: control-flow procedures with `numLocals > 0` are not yet supported"

    let goal ← rewriteZeroLocalsGoalToBody goal
    let parsed ← parseExecGoal goal
    let some (idx, boundary) ← firstControlBoundary? parsed.opExprs
      | return ← runOnGoal goal (← `(tactic| miden_reflect))

    if parsed.opExprs.size > 1 then
      return ← decomposeAppendGoalAt goal (if idx = 0 then 1 else idx)

    match boundary with
    | .ifElse thenOps elseOps =>
        let (goal, bridgeSeeds) ← canonicalizeVcgGoal goal (closeBridges := false)
        let parsed ← parseExecGoal goal
        let condExpr ← mkFreshExprMVar (Lean.mkConst ``MidenLean.Felt)
        let restExpr ← mkFreshExprMVar
          (Lean.mkApp (Lean.mkConst ``List [Lean.levelZero]) (Lean.mkConst ``MidenLean.Felt))
        let finalStateExpr ← mkFreshExprMVar (Lean.mkConst ``MidenLean.Concrete.State)
        let theoremExpr := Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure_ifElse_eq)
          #[parsed.envExpr, parsed.fuelExpr, thenOps, elseOps,
            parsed.stateExpr, finalStateExpr, condExpr, restExpr]
        let goals ←
          try
            goal.apply theoremExpr
          catch ex =>
            throwError "miden_vcg: failed to decompose singleton `ifElse`: {ex.toMessageData}"
        let mut hsGoal? : Option MVarId := none
        let mut hfuelGoal? : Option MVarId := none
        let mut branchGoals : List MVarId := []
        let mut hboolGoal? : Option MVarId := none
        let mut auxGoals : List MVarId := []
        for g in goals do
          unless ← g.isAssigned do
            let ty ← g.getType
            if ← isProp ty then
              match ty.eq? with
              | some (_, lhs, rhs) =>
                  if (← hasListTypeOf lhs ``MidenLean.Felt) || (← hasListTypeOf rhs ``MidenLean.Felt) then
                    hsGoal? := some g
                  else
                    auxGoals := auxGoals ++ [g]
              | none =>
                  if ty.isForall then
                    branchGoals := branchGoals ++ [g]
                  else if ty.isAppOfArity ``Or 2 then
                    hboolGoal? := some g
                  else
                    hfuelGoal? := some g
            else
              auxGoals := auxGoals ++ [g]
        let some hsGoal := hsGoal? | throwError "miden_vcg: missing `hs` goal for singleton `ifElse`"
        let some hfuelGoal := hfuelGoal? | throwError "miden_vcg: missing `hfuel` goal for singleton `ifElse`"
        let [branchGoal1, branchGoal2] := branchGoals
          | throwError "miden_vcg: expected two branch goals for singleton `ifElse`, got {branchGoals.length}"
        let some hboolGoal := hboolGoal? | throwError "miden_vcg: missing `hbool` goal for singleton `ifElse`"
        closeVcgStackGoal hsGoal
        closeVcgFuelGoal hfuelGoal
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
        let (_, branchBodyGoal1) ← branchGoal1.intro1
        let (_, branchBodyGoal2) ← branchGoal2.intro1
        let branch1IsThen ← branchBodyMatches branchBodyGoal1 thenOps
        let branch1IsElse ← branchBodyMatches branchBodyGoal1 elseOps
        let branch2IsThen ← branchBodyMatches branchBodyGoal2 thenOps
        let branch2IsElse ← branchBodyMatches branchBodyGoal2 elseOps
        let (hthenBodyGoal, helseBodyGoal) ←
          if branch1IsThen && branch2IsElse then
            pure (branchBodyGoal1, branchBodyGoal2)
          else if branch1IsElse && branch2IsThen then
            pure (branchBodyGoal2, branchBodyGoal1)
          else
            throwError "miden_vcg: could not classify singleton `ifElse` branch goals"
        let thenRemaining ← decomposeVcgGoal hthenBodyGoal
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
        let elseRemaining ← decomposeVcgGoal helseBodyGoal
        let boolRemaining ← closeVcgBoolGoal hboolGoal
        let auxRemaining ← cleanupGoals auxGoals
        return thenRemaining ++ elseRemaining ++ boolRemaining ++ auxRemaining ++ bridgeSeeds
    | .repeat countExpr bodyOps =>
        let some count := countExpr.numeral?
          | throwError "miden_vcg: `repeat` count must reduce to a Nat literal"
        if count = 0 then
          let theoremExpr := Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure_repeat_zero_eq)
            #[parsed.envExpr, parsed.fuelExpr, bodyOps, parsed.stateExpr]
          let rwResult ←
            try
              goal.rewrite (← goal.getType) theoremExpr
            catch ex =>
              throwError "miden_vcg: failed to decompose singleton `repeat 0`: {ex.toMessageData}"
          let goal' ← goal.replaceTargetEq rwResult.eNew rwResult.eqProof
          let mut hfuelGoal? : Option MVarId := none
          let mut auxGoals : List MVarId := [goal']
          for g in rwResult.mvarIds do
            unless ← g.isAssigned do
              let ty ← g.getType
              if ← isProp ty then
                hfuelGoal? := some g
              else
                auxGoals := auxGoals ++ [g]
          let some hfuelGoal := hfuelGoal? | throwError "miden_vcg: missing `hfuel` goal for singleton `repeat 0`"
          closeVcgFuelGoal hfuelGoal
          let mut bridgeSeeds : List MVarId := []
          let mut otherGoals : List MVarId := []
          for g in auxGoals do
            unless ← g.isAssigned do
              let ty ← g.getType
              if ty.eq?.isSome then
                bridgeSeeds := bridgeSeeds ++ [g]
              else
                otherGoals := otherGoals ++ [g]
          let mut bridgeRemaining : List MVarId := []
          for g in bridgeSeeds do
            bridgeRemaining := bridgeRemaining ++ (← closeBridgeGoal g)
          cleanupGoals (bridgeRemaining ++ otherGoals)
        else
          let theoremExpr := Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure_repeat_succ_eq)
            #[parsed.envExpr, parsed.fuelExpr, Lean.mkNatLit (count - 1), bodyOps]
          let goals ←
            try
              goal.apply theoremExpr
            catch ex =>
              throwError "miden_vcg: failed to decompose singleton `repeat`: {ex.toMessageData}"
          let mut hfuelGoal? : Option MVarId := none
          let mut execGoals : List MVarId := []
          let mut auxGoals : List MVarId := []
          for g in goals do
            unless ← g.isAssigned do
              let ty ← g.getType
              if ← isProp ty then
                match ty.eq? with
                | some _ => execGoals := execGoals ++ [g]
                | none => hfuelGoal? := some g
              else
                auxGoals := auxGoals ++ [g]
          let some hfuelGoal := hfuelGoal? | throwError "miden_vcg: missing `hfuel` goal for singleton `repeat`"
          let [execGoal1, execGoal2] := execGoals
            | throwError "miden_vcg: expected two execution goals for singleton `repeat`, got {execGoals.length}"
          let restOpsExpr ← mkOpListExpr [Lean.mkAppN (Lean.mkConst ``MidenLean.Op.repeat)
            #[Lean.mkNatLit (count - 1), bodyOps]]
          let goal1IsBody ← branchBodyMatches execGoal1 bodyOps
          let goal1IsRest ← branchBodyMatches execGoal1 restOpsExpr
          let goal2IsBody ← branchBodyMatches execGoal2 bodyOps
          let goal2IsRest ← branchBodyMatches execGoal2 restOpsExpr
          let (bodyGoal, restGoal) ←
            if goal1IsBody && goal2IsRest then
              pure (execGoal1, execGoal2)
            else if goal1IsRest && goal2IsBody then
              pure (execGoal2, execGoal1)
            else
              throwError "miden_vcg: could not classify singleton `repeat` goals"
          closeVcgFuelGoal hfuelGoal
          let bodyRemaining ← decomposeVcgGoal bodyGoal
          Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
          let restRemaining ← decomposeVcgGoal restGoal
          let auxRemaining ← cleanupGoals auxGoals
          return bodyRemaining ++ restRemaining ++ auxRemaining
    | .whileTrue _ =>
        throwError "miden_vcg: `whileTrue` is not yet supported. Use manual proofs with invariants."

end

/-- `miden_vcg` recursively decomposes equality goals over control-flow bodies,
    delegating straight-line leaves to `miden_reflect`. Supported control flow:
    `ifElse` and concrete-count `repeat`. `whileTrue` remains unsupported. -/
syntax "miden_vcg" : tactic
elab_rules : tactic
  | `(tactic| miden_vcg) => do
      let mainGoal ← getMainGoal
      let remaining ← decomposeVcgGoal mainGoal
      setGoals remaining
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing

end MidenLean.Symbolic.Tactic
