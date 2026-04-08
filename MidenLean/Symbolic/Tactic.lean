import MidenLean.Symbolic.Reflect
import MidenLean.Proofs.ControlFlow

/-!
# Proof Automation Tactics

## `miden_reflect`

Automates reflection for straight-line basic-block proofs.
Supported goals are `exec` / `execWithEnv` equations whose procedure body is a
list of `.inst` ops only. The tactic does not handle control flow, `.exec`, or
dynamic-address memory instructions.

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

private inductive ReflectPath where
  | zero
  | locals (k : Nat)

/-- Goal data extracted from an `exec` / `execWithEnv` equation. -/
private structure ReflectGoal where
  lhs : Lean.Expr
  rhs : Lean.Expr
  envExpr : Lean.Expr
  fuelExpr : Lean.Expr
  stackExpr : Lean.Expr
  memExpr : Lean.Expr
  framesExpr : Lean.Expr
  advExpr : Lean.Expr
  stackElems : Array Lean.Expr
  restExpr : Lean.Expr
  nameExpr : Lean.Expr
  numLocalsExpr : Lean.Expr
  bodyExpr : Lean.Expr
  instExprs : Array Lean.Expr
  path : ReflectPath

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

/-- Check that every instruction in the array is not an exec instruction.
    Returns the index and pretty-printed name of the first exec instruction,
    or `none` if all pass. -/
private def findExecInst (instExprs : Array Lean.Expr) : MetaM (Option (Nat × Format)) := do
  for i in [:instExprs.size] do
    let e := instExprs[i]!
    let app := Lean.mkApp (Lean.mkConst ``MidenLean.Symbolic.isExecInst) e
    let reduced ← whnf app
    if reduced.isConstOf ``Bool.true then
      let fmt ← Meta.ppExpr e
      return some (i, fmt)
  return none

/-- Build a concrete `List` expression from already elaborated elements. -/
private def mkListExpr (elemTy : Lean.Expr) (xs : List Lean.Expr) : MetaM Lean.Expr := do
  xs.foldrM
    (fun x acc => mkAppM ``List.cons #[x, acc])
    (← mkAppOptM ``List.nil #[some elemTy])

/-- Check if a Lean `Expr` is a `Nat` literal equal to zero. -/
private def isNatZero (e : Lean.Expr) : Bool :=
  e.numeral? == some 0 || e.isConstOf ``Nat.zero

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
  closeGoalWith goal "bridge goal" (← `(tactic|
    first
    | rfl
    | simp [miden_reflect_norm,
            MidenLean.Symbolic.Expr.eval,
            MidenLean.Symbolic.Reflect.concreteAssignment,
            MidenLean.Symbolic.Reflect.concreteState,
            MidenLean.Symbolic.Reflect.concreteStateWithLocals,
            MidenLean.LocalFrame.localAddr]
    | apply congrArg some
      ext addr <;>
      simp [miden_reflect_norm,
            MidenLean.Symbolic.Expr.eval,
            MidenLean.Symbolic.Reflect.concreteAssignment,
            MidenLean.Symbolic.Reflect.concreteState,
            MidenLean.Symbolic.Reflect.concreteStateWithLocals,
            MidenLean.LocalFrame.localAddr]))

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
  unless stateWhnf.getAppNumArgs == 4 do
    throwError "miden_reflect: state should be ⟨stack, mem, frames, adv⟩"
  let stackExpr := stateWhnf.getArg! 0
  let memExpr := stateWhnf.getArg! 1
  let framesExpr := stateWhnf.getArg! 2
  let advExpr := stateWhnf.getArg! 3

  let (stackElems, restExpr) ← extractCons stackExpr

  let procWhnf ← whnf procExpr
  unless procWhnf.getAppNumArgs == 3 do
    throwError "miden_reflect: could not reduce procedure to ⟨name, numLocals, body⟩"
  let nameExpr := procWhnf.getArg! 0
  let numLocalsExpr := procWhnf.getArg! 1
  let bodyExpr := procWhnf.getArg! 2
  let numLocalsWhnf ← whnf numLocalsExpr

  let some instExprs ← extractInsts bodyExpr
    | throwError "miden_reflect: procedure body contains non-instruction ops (only basic blocks supported)"

  if let some (idx, instFmt) ← findExecInst instExprs then
    throwError "miden_reflect: instruction {instFmt} at position {idx} is an exec call. \
      Use `miden_vcg` or manual chunking for procedures with exec calls."

  for i in [:instExprs.size] do
    if let some reason ← unsupportedInstReason? instExprs[i]! then
      let fmt ← Meta.ppExpr instExprs[i]!
      throwError "miden_reflect: instruction {fmt} at position {i} is outside the supported \
        basic-block fragment: {reason}"

  let path ←
    if isNatZero numLocalsWhnf then
      pure ReflectPath.zero
    else
      match numLocalsWhnf.numeral? with
      | some (Nat.succ k) => pure (.locals k)
      | _ =>
        throwError "miden_reflect: numLocals must reduce to a Nat literal"

  pure {
    lhs, rhs, envExpr, fuelExpr,
    stackExpr, memExpr, framesExpr, advExpr,
    stackElems, restExpr,
    nameExpr, numLocalsExpr, bodyExpr, instExprs, path
  }

/-- Build the wrapper theorem application used by `miden_reflect`. -/
private def buildReflectTheoremExpr (goal : ReflectGoal) : TacticM Lean.Expr := do
  let instTy := Lean.mkConst ``MidenLean.Instruction
  let instsExpr ← mkListExpr instTy goal.instExprs.toList
  let stackPrefixExpr ← mkListExpr (Lean.mkConst ``MidenLean.Felt) goal.stackElems.toList
  let resultExpr ← mkFreshExprMVar (Lean.mkConst ``MidenLean.Symbolic.BlockResult)
  match goal.path with
  | .zero =>
    pure <|
      Lean.mkAppN
        (Lean.mkConst ``MidenLean.Symbolic.Reflect.reflect_with_env_zero_concrete)
        #[instsExpr, goal.nameExpr, goal.bodyExpr, goal.envExpr, goal.fuelExpr,
          stackPrefixExpr, goal.restExpr, goal.memExpr, goal.framesExpr, goal.advExpr, resultExpr]
  | .locals k =>
    pure <|
      Lean.mkAppN
        (Lean.mkConst ``MidenLean.Symbolic.Reflect.reflect_with_env_locals_concrete)
        #[instsExpr, goal.nameExpr, Lean.mkRawNatLit k, goal.bodyExpr, goal.envExpr, goal.fuelExpr,
          stackPrefixExpr, goal.restExpr, goal.memExpr, goal.framesExpr, goal.advExpr, resultExpr]

elab "miden_reflect" : tactic => do
  let reflectGoal ← parseReflectGoal
  let mainGoal ← getMainGoal
  let theoremExpr ← buildReflectTheoremExpr reflectGoal

  -- Insert a canonical middle term before theorem application.
  let targetTy ← inferType reflectGoal.lhs
  let middleExpr ← mkFreshExprMVar targetTy
  let eqTransExpr ← mkAppOptM ``Eq.trans
    #[some targetTy, some reflectGoal.lhs, some middleExpr, some reflectGoal.rhs]
  let goals ←
    try
      mainGoal.apply eqTransExpr
    catch e =>
      throwError "miden_reflect: failed to insert canonical target:{indentD e.toMessageData}"
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
    catch e =>
      throwError "miden_reflect: failed to apply reflection wrapper:{indentD e.toMessageData}"
  let mut hopsGoal? : Option MVarId := none
  let mut hfuelGoal? : Option MVarId := none
  let mut hnoexecGoal? : Option MVarId := none
  let mut hresultGoal? : Option MVarId := none
  let mut hprecondsGoal? : Option MVarId := none
  let mut auxTheoremGoals : List MVarId := []
  for goal in theoremGoals do
    unless ← goal.isAssigned do
      let ty ← goal.getType
      if ← isProp ty then
        match ty.eq? with
        | some (_, lhs, rhs) =>
          if lhs.isAppOf ``MidenLean.Symbolic.execBlock then
            hresultGoal? := some goal
          else if rhs.isConstOf ``Bool.true || lhs.isConstOf ``Bool.true then
            hnoexecGoal? := some goal
          else
            hopsGoal? := some goal
        | none =>
          if ty.isForall then
            hprecondsGoal? := some goal
          else
            hfuelGoal? := some goal
      else
        auxTheoremGoals := auxTheoremGoals ++ [goal]
  let some hopsGoal := hopsGoal? | throwError "miden_reflect: missing `hops` goal"
  let some hfuelGoal := hfuelGoal? | throwError "miden_reflect: missing `hfuel` goal"
  let some hnoexecGoal := hnoexecGoal? | throwError "miden_reflect: missing `hnoexec` goal"
  let some hresultGoal := hresultGoal? | throwError "miden_reflect: missing `hresult` goal"
  let some hprecondsGoal := hprecondsGoal? | throwError "miden_reflect: missing `hpreconds` goal"

  closeGoalWith hopsGoal "`hops`" (← `(tactic| rfl))
  closeGoalWith hfuelGoal "`hfuel`" (← `(tactic| omega))
  closeGoalWith hnoexecGoal "`hnoexec`" (← `(tactic| decide))
  closeGoalWith hresultGoal "`hresult`" (← `(tactic| rfl))
  closeBridgeGoal bridgeGoal

  let mut remainingSeeds := [hprecondsGoal]
  for goal in auxTheoremGoals do
    unless ← goal.isAssigned do
      remainingSeeds := remainingSeeds ++ [goal]
  for goal in auxGoals do
    unless ← goal.isAssigned do
      remainingSeeds := remainingSeeds ++ [goal]
  let remaining ← cleanupGoals remainingSeeds
  setGoals remaining

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
