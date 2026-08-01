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
- **`Op.repeat`**: applies `execProcedure_repeat_succ`, generating body and rest subgoals
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

private def mkOpListExpr (xs : List Lean.Expr) : MetaM Lean.Expr :=
  mkListExpr (Lean.mkConst ``MidenLean.Op) xs

private def mkListExprWithTail (xs : List Lean.Expr) (tail : Lean.Expr) : MetaM Lean.Expr := do
  xs.foldrM (fun x acc => mkAppM ``List.cons #[x, acc]) tail

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

private def getStateStackDecomposition (stateExpr : Lean.Expr) : TacticM (Array Lean.Expr × Lean.Expr) := do
  let stateWhnf ← whnf stateExpr
  if stateWhnf.getAppNumArgs == 4 then
    let stackExpr := stateWhnf.getArg! 0
    extractCons stackExpr
  else
    let stackExpr := Lean.mkProj ``MidenLean.Concrete.State 0 stateExpr
    let stackProjWhnf ← whnf stackExpr
    if stateExpr.isAppOfArity ``MidenLean.Concrete.State.withStack 2 ||
        stackProjWhnf.isAppOfArity ``List.nil 1 ||
        stackProjWhnf.isAppOfArity ``List.cons 2 then
      extractCons stackExpr
    else
      findStackDecomposition stateExpr

/-- Run a tactic against a single goal and return the remaining goals. -/
private def runOnGoal (goal : MVarId) (stx : TSyntax `tactic) : TacticM (List MVarId) := do
  if ← goal.isAssigned then
    pure []
  else
    setGoals [goal]
    evalTactic stx
    return ← getGoals

/-- Run a tactic sequence against a single goal and return the remaining goals. -/
private def runTacticSeqOnGoal (goal : MVarId) (stx : TSyntax `Lean.Parser.Tactic.tacticSeq) :
    TacticM (List MVarId) := do
  if ← goal.isAssigned then
    pure []
  else
    goal.withContext do
      setGoals [goal]
      evalTactic stx
      return ← getGoals

/-- Run a tactic on a goal and attach a short label if it throws. -/
private def runNamedOnGoal (label : String) (goal : MVarId) (stx : TSyntax `tactic) :
    TacticM (List MVarId) := do
  try
    runOnGoal goal stx
  catch ex =>
    let ty ← goal.getType
    throwError "{label} failed on goal:{indentExpr ty}\n{ex.toMessageData}"

/-- Try running a tactic on a goal. On failure, restore the previous state and return `none`. -/
private def tryRunOnGoal? (goal : MVarId) (stx : TSyntax `tactic) :
    TacticM (Option (List MVarId)) := do
  let savedState ← saveState
  try
    return some (← runOnGoal goal stx)
  catch _ =>
    restoreState savedState
    return none

private def tryRunTacticSeqOnGoal? (goal : MVarId) (stx : TSyntax `Lean.Parser.Tactic.tacticSeq) :
    TacticM (Option (List MVarId)) := do
  let savedState ← saveState
  try
    return some (← runTacticSeqOnGoal goal stx)
  catch _ =>
    restoreState savedState
    return none

/-- Solve a goal completely with the provided tactic script. -/
private def closeGoalWith (goal : MVarId) (label : String) (stx : TSyntax `tactic) : TacticM Unit := do
  unless ← goal.isAssigned do
    let remaining ←
      try
        runOnGoal goal stx
      catch ex =>
        let ty ← goal.getType
        throwError "miden_reflect: failed to solve {label}:{indentExpr ty}\n{ex.toMessageData}"
    unless remaining.isEmpty do
      let ty ← remaining[0]!.getType
      throwError "miden_reflect: failed to solve {label}:{indentExpr ty}"

/-- Close an equality goal whose one side (or `Option.some` argument) is a
    bare unassigned metavariable, by unifying the two sides. Unification runs
    through `isDefEq` rather than a raw `MVarId.assign`, so the occurs, scope,
    and type checks apply: an illegal assignment leaves the goal open for the
    caller instead of producing an ill-typed term that only the kernel
    rejects. -/
private def closeEqByAssigningMVar? (goal : MVarId) : TacticM Bool := do
  if ← goal.isAssigned then
    return true
  goal.withContext do
    let ty ← goal.getType
    let some (_, lhs, rhs) := ty.eq?
      | return false
    let unassignedMVar (e : Lean.Expr) : TacticM Bool := do
      if e.isMVar then
        return !(← e.mvarId!.isAssigned)
      return false
    let mut assignable := (← unassignedMVar lhs) || (← unassignedMVar rhs)
    if !assignable
        && lhs.isAppOfArity ``Option.some 2 && rhs.isAppOfArity ``Option.some 2 then
      assignable := (← unassignedMVar (lhs.getArg! 1)) || (← unassignedMVar (rhs.getArg! 1))
    unless assignable do
      return false
    let unified ←
      try
        isDefEq lhs rhs
      catch _ =>
        pure false
    unless unified do
      return false
    goal.assign (← mkEqRefl (← instantiateMVars rhs))
    return true

private def closeReflectResultGoal (goal : MVarId) : TacticM Unit := do
  unless ← goal.isAssigned do
    -- Fast path: `whnf` (at full transparency) each side just enough to
    -- expose the `Option.some (concreteState ...)` head, then match it
    -- against the other side. Unlike `Meta.reduce`, `whnf` does NOT
    -- recursively normalize argument subterms, so it never descends into
    -- the `Felt.ofNat (<complex-Nat>)` expressions that make up the stack
    -- elements — avoiding the `maxRecDepth` blow-up from deeply nested
    -- `ZMod.val`/`Nat.div`/`Nat.mod` reduction.
    let tryWhnf : TacticM Bool := do
      let ty ← goal.getType
      let some (_, lhs, rhs) := ty.eq?
        | return false
      let lhs' ← withTransparency TransparencyMode.all <| whnf lhs
      let rhs' ← withTransparency TransparencyMode.all <| whnf rhs
      -- `isDefEq` also covers the `some ?m = some (concreteState ...)` case:
      -- it unifies the metavariable argument with the other side, with the
      -- occurs/scope/type checks a raw `MVarId.assign` would skip.
      if ← isDefEq lhs' rhs' then
        goal.assign (← mkEqRefl (← instantiateMVars lhs'))
        return true
      return false
    if ← tryWhnf then
      pure ()
    else
      let remaining ← runNamedOnGoal "miden_reflect.closeReflectResultGoal" goal (← `(tactic|
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

/-- A `valLeq _ 63` precondition holds for a literal shift below 64
    (discharges `pow2`-style shift bounds during cleanup). Scoped to
    `miden_bound` — too specialized for the global default simp set. -/
@[miden_bound] private theorem holdsValLeqLit63ConcreteOfLt64
    (shift : MidenLean.Felt) (hlt : shift.val < 64) :
    (MidenLean.Symbolic.Precondition.valLeq (MidenLean.Symbolic.Expr.lit shift) 63).holds
      MidenLean.Symbolic.Reflect.concreteAssignment := by
  unfold MidenLean.Symbolic.Precondition.holds
  simp [MidenLean.Symbolic.Expr.eval]
  omega

@[miden_bound] private theorem u32OverflowingSub64SndValLe63
    (shift : MidenLean.Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift_ge64 : ¬ shift.val < 64)
    (hshift_lt128 : shift.val < 128) :
    (MidenLean.Felt.ofNat (MidenLean.u32OverflowingSub shift.val 64).2).val ≤ 63 := by
  have hlt : (MidenLean.Felt.ofNat (MidenLean.u32OverflowingSub shift.val 64).2).val < 64 := by
    exact MidenLean.u32OverflowingSub64_snd_val_lt_64 shift hshift_u32 hshift_ge64 hshift_lt128
  omega

@[miden_bound] private theorem holdsValLeqU32WSubLit64Concrete
    (shift : MidenLean.Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift_ge64 : ¬ shift.val < 64)
    (hshift_lt128 : shift.val < 128) :
    (MidenLean.Symbolic.Precondition.valLeq
        ((MidenLean.Symbolic.Expr.lit shift).u32WSub (MidenLean.Symbolic.Expr.lit 64)) 63).holds
      MidenLean.Symbolic.Reflect.concreteAssignment := by
  unfold MidenLean.Symbolic.Precondition.holds
  simp [MidenLean.Symbolic.Expr.eval]
  exact u32OverflowingSub64SndValLe63 shift hshift_u32 hshift_ge64 hshift_lt128

/-- Apply light cleanup to remaining goals, closing trivial `hpreconds` goals. -/
private def finalizeCleanupGoals (goals : List MVarId) : TacticM (List MVarId) := do
  let mut remaining : List MVarId := []
  for goal in goals do
    unless ← goal.isAssigned do
      if let some rem ← tryRunOnGoal? goal (← `(tactic| assumption)) then
        remaining := remaining ++ rem
      else if let some rem ← tryRunOnGoal? goal (← `(tactic| rfl)) then
        remaining := remaining ++ rem
      else if let some rem ← tryRunTacticSeqOnGoal? goal (← `(tacticSeq|
        intros p hp
        simp at hp
        repeat' (first | rcases hp with rfl | hp)
        all_goals (simp [miden_reflect_norm, miden_u32, miden_val, miden_bound, *] at *)
        all_goals (first | rfl | miden_arith | omega))) then
        remaining := remaining ++ rem
      else if let some rem ← tryRunOnGoal? goal (← `(tactic|
        first
        | simp [miden_reflect_norm, miden_cleanup,
                miden_u32, miden_val, miden_bound, *]
        | miden_finish_reflection)) then
        remaining := remaining ++ rem
      else if let some rem ← tryRunOnGoal? goal (← `(tactic| tauto)) then
        remaining := remaining ++ rem
      else if let some rem ← tryRunOnGoal? goal (← `(tactic| omega)) then
        remaining := remaining ++ rem
      else if let some rem ← tryRunOnGoal? goal (← `(tactic| miden_arith)) then
        remaining := remaining ++ rem
      else
        remaining := remaining ++ [goal]
  return remaining

/-- Main cleanup ladder for residual VCG goals: hypothesis lookup, `decide`,
    if-splitting, precondition normalization, then arithmetic. Whatever
    survives is handed to `finalizeCleanupGoals`. -/
private def cleanupGoals (goals : List MVarId) : TacticM (List MVarId) := do
  let mut remaining : List MVarId := []
  for goal in goals do
    unless ← goal.isAssigned do
      if let some rem ← tryRunOnGoal? goal (← `(tactic| assumption)) then
        remaining := remaining ++ rem
      else if let some rem ← tryRunTacticSeqOnGoal? goal (← `(tacticSeq|
        symm
        assumption)) then
        remaining := remaining ++ rem
      else if let some rem ← tryRunOnGoal? goal (← `(tactic| decide)) then
        remaining := remaining ++ rem
      else if let some rem ← tryRunOnGoal? goal (← `(tactic| split_ifs at * <;> simp_all)) then
        remaining := remaining ++ rem
      else if let some rem ← tryRunTacticSeqOnGoal? goal (← `(tacticSeq|
        intros p hp
        simp only [List.mem_cons, List.mem_append, List.mem_singleton,
                   true_and, and_true,
                   and_assoc, and_left_comm, and_comm,
                   or_assoc, or_left_comm, or_comm,
                   miden_reflect_norm,
                   MidenLean.Symbolic.Precondition.holds,
                   MidenLean.Symbolic.Expr.eval,
                   MidenLean.Symbolic.Reflect.concreteAssignment,
                   miden_u32, miden_val, miden_bound, *] at hp ⊢
        first
        | tauto
        | miden_arith
        | omega)) then
        remaining := remaining ++ rem
      else if let some rem ← tryRunOnGoal? goal (← `(tactic|
        split_ifs at * <;> simp [MidenLean.Concrete.State.withStack] at *)) then
        remaining := remaining ++ rem
      else if let some rem ← tryRunOnGoal? goal (← `(tactic| tauto)) then
        remaining := remaining ++ rem
      else if let some rem ← tryRunOnGoal? goal (← `(tactic| omega)) then
        remaining := remaining ++ rem
      else if let some rem ← tryRunOnGoal? goal (← `(tactic| miden_arith)) then
        remaining := remaining ++ rem
      else if let some rem ← tryRunOnGoal? goal (← `(tactic|
        simp only [true_and, and_true, miden_u32, miden_val, miden_bound, *])) then
        remaining := remaining ++ rem
      else
        remaining := remaining ++ [goal]
  finalizeCleanupGoals remaining

/-- Cleanup for goals produced by theorem-backed singleton `.exec` summaries.
    This path needs stronger arithmetic normalization than plain `cleanupGoals`
    because callee summaries often leave `isU32` side conditions on derived
    values such as `lo32`/`hi32` limbs of `Felt.ofNat` expressions. -/
private def cleanupExecSummaryGoals (goals : List MVarId) : TacticM (List MVarId) := do
  let mut remaining : List MVarId := []
  for goal in goals do
    unless ← goal.isAssigned do
      if let some rem ← tryRunOnGoal? goal (← `(tactic|
        first
        | assumption
        | symm; assumption
        | rfl
        | decide
        | omega
        | miden_arith
        | simp only [miden_u32, miden_val, miden_bound, *]
        | simp [miden_reflect_norm, miden_cleanup]
        | miden_finish_reflection)) then
        remaining := remaining ++ rem
      else
        remaining := remaining ++ [goal]
  cleanupGoals remaining

/-- Simplify the bridge between the tactic's canonical reflected target and the
    user goal, directly instantiating state metavariables when possible. -/
private def closeBridgeGoal (goal : MVarId) : TacticM (List MVarId) := do
  if ← goal.isAssigned then
    pure []
  else
    if ← closeEqByAssigningMVar? goal then
      return []
    let remaining ← runNamedOnGoal "miden_vcg.closeBridgeGoal" goal (← `(tactic|
      first
      | assumption
      | symm; assumption
      | rfl
      | simp [MidenLean.Concrete.State.withStack]))
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
  | Option.some _ callee => pure (some callee)
  | _ => pure none

/-- Walk past leading binders in a theorem type to find the conclusion. -/
private def conclusionOfType (ty : Lean.Expr) : MetaM Lean.Expr :=
  Meta.forallTelescopeReducing ty fun _ body => pure body

/-- Extract metadata from a theorem whose conclusion has the form
    `execProcedure env fuel state callee = some result`. Returns the head
    constant of `callee`, plus a flag indicating whether the `fuel` argument
    is parametric (bound by an outer forall) rather than a concrete literal. -/
private def extractCalleeFromType (ty : Lean.Expr) :
    MetaM (Option (Lean.Name × Bool)) := do
  Meta.forallTelescopeReducing ty fun fvars body => do
    let some (_, lhs, _) := body.eq? | return none
    unless lhs.isAppOf ``MidenLean.execProcedure && lhs.getAppNumArgs == 4 do
      return none
    -- Do NOT whnf the procedure expression — that would unfold the constant
    -- (e.g. `Miden.Core.U64.overflowing_add`) into its `Procedure.mk` body,
    -- losing the name we want to match on.
    let some calleeName := (lhs.getArg! 3).getAppFn.constName? | return none
    let fuelArg := lhs.getArg! 1
    -- A theorem is "parametric" in fuel if the fuel position depends on a
    -- bound forall variable (e.g. `fuel + 1`), as opposed to a concrete
    -- literal like `10`.
    let fuelIsParametric := fvars.any (fun fv => fuelArg.containsFVar fv.fvarId!)
    return some (calleeName, fuelIsParametric)

/-- Find all `@[miden_exec_summary]` theorems whose conclusion targets the
    given callee procedure constant. The returned array is ordered so that
    theorems with parametric fuel (e.g. `_run` form, accepting any `fuel + 1`)
    come before theorems with a concrete fuel literal (e.g. `_exec` form,
    fixed at `10`). This lets the registry pick the most flexible candidate
    first when the goal's fuel was decremented by an `execProcedure_append_eq`
    bridge upstream. -/
private def findExecSummaryTheorems (calleeName : Lean.Name) :
    MetaM (Array Lean.Name) := do
  let env ← getEnv
  let allTheorems := MidenLean.Symbolic.getExecSummaryTheorems env
  let mut parametric : Array Lean.Name := #[]
  let mut concrete : Array Lean.Name := #[]
  for thmName in allTheorems do
    try
      let info ← getConstInfo thmName
      if let some (name, isParam) ← extractCalleeFromType info.type then
        if name == calleeName then
          if isParam then
            parametric := parametric.push thmName
          else
            concrete := concrete.push thmName
    catch _ => pure ()
  return parametric ++ concrete

/-- Look up a theorem-backed callee execution summary from the
    `@[miden_exec_summary]` registry. Returns the candidates in preference
    order (parametric fuel first). -/
private def registryExecTheoremNames
    (calleeExpr : Lean.Expr) : MetaM (Array Lean.Name) := do
  -- `concreteCalleeExpr?` already returns a `whnf`-reduced expression. We expect
  -- it to be a constant like `Miden.Core.U64.overflowing_add`; do NOT `whnf`
  -- again here because that would unfold the constant into its body.
  let some calleeName := calleeExpr.getAppFn.constName? | return #[]
  findExecSummaryTheorems calleeName

/-- Parse the current goal as an `execProcedure` equation with a concrete op list. -/
private def parseExecGoal (goal : MVarId) : TacticM ExecGoal := do
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

private def cleanupExecBridgeGoals (goals : List MVarId) : TacticM (List MVarId) := do
  let mut remaining : List MVarId := []
  for g in goals do
    unless ← g.isAssigned do
      let rem ←
        runNamedOnGoal "miden_vcg.cleanupExecBridgeGoals" g (← `(tactic|
          first
          | assumption
          | symm; assumption
          | rfl
          | omega
          | simp))
      remaining := remaining ++ rem
  pure remaining

private def applyExecSummaryTheoremRaw?
    (goal : MVarId) (theoremName : Lean.Name) : TacticM (Option (List MVarId)) := do
  let theoremExpr ← goal.withContext do
    let lctx ← getLCtx
    let localExpr? : Option Lean.Expr ← lctx.findDeclM? fun decl => do
      pure <| if !decl.isImplementationDetail && decl.userName == theoremName then
        some (Lean.mkFVar decl.fvarId)
      else
        none
    pure <| match localExpr? with
      | some expr => expr
      | none => Lean.mkConst theoremName
  let theoremGoals ←
    try
      goal.apply theoremExpr
    catch _ =>
      return none
  let mut remaining : List MVarId := []
  for g in theoremGoals do
    unless ← g.isAssigned do
      remaining := remaining ++ [g]
  pure (some remaining)

private def rewriteGoalWithTheorem
    (goal : MVarId) (thmExpr : Lean.Expr) : TacticM (MVarId × List MVarId) := do
  let goalTy ← goal.getType
  let result ← goal.rewrite goalTy thmExpr
  let newGoal ← goal.replaceTargetEq result.eNew result.eqProof
  pure (newGoal, result.mvarIds)

private def buildExecSummaryProofExpr
    (theoremName : Lean.Name)
    (envExpr fuelExpr stateExpr calleeExpr : Lean.Expr) :
    TacticM (Lean.Expr × List MVarId) := do
  let directCallExpr := Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure)
    #[envExpr, fuelExpr, stateExpr, calleeExpr]
  let directCallTy ← inferType directCallExpr
  let resultExpr ← mkFreshExprMVar directCallTy
  let proofGoalType ← mkEq directCallExpr resultExpr
  let proofGoalExpr ← mkFreshExprMVar proofGoalType
  let some theoremGoals ← applyExecSummaryTheoremRaw? proofGoalExpr.mvarId! theoremName
    | throwError "miden_exec_step: `{theoremName}` did not apply to the exposed direct callee"
  pure (proofGoalExpr, theoremGoals)

private def rewriteGoalWithSingletonExecBridge
    (goal : MVarId)
    (envExpr fuelExpr stateExpr targetExpr calleeExpr : Lean.Expr) :
    TacticM (MVarId × List MVarId) := do
  let someCalleeExpr ← mkAppM ``Option.some #[calleeExpr]
  let hlookupType ← mkEq (Lean.mkApp envExpr targetExpr) someCalleeExpr
  let hlookupExpr ← mkFreshExprMVar hlookupType
  let hfuelType ← mkAppM ``LT.lt #[Lean.mkNatLit 0, fuelExpr]
  let hfuelExpr ← mkFreshExprMVar hfuelType
  let bridgeExpr := Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure_singleton_exec_state)
    #[envExpr, fuelExpr, stateExpr, targetExpr, calleeExpr, hlookupExpr, hfuelExpr]
  rewriteGoalWithTheorem goal bridgeExpr

private inductive ExecSummaryStep where
  | direct (goal : MVarId) (theoremName : Lean.Name)
      (envExpr fuelExpr stateExpr calleeExpr : Lean.Expr)
  | nested (goal : MVarId) (theoremName : Lean.Name)
      (envExpr fuelExpr stateExpr calleeExpr : Lean.Expr)

private def runExecSummaryStep : ExecSummaryStep → TacticM (List MVarId)
  | .direct goal theoremName envExpr fuelExpr stateExpr calleeExpr => do
      let (proofExpr, theoremSideGoals) ←
        buildExecSummaryProofExpr theoremName envExpr fuelExpr stateExpr calleeExpr
      -- A checked assign unifies the goal's RHS (often a bare intermediate-state
      -- metavariable from an append split) with the summary's result state. A raw
      -- `assign` would leave that metavariable free for downstream goals to
      -- mis-unify with the original state via `hs`.
      -- Unify the goal's RHS (often a bare intermediate-state metavariable from
      -- an append split) with the summary's result state before assigning. A
      -- raw `assign` would leave that metavariable free for downstream goals
      -- to mis-unify with the original state via `hs`.
      goal.withContext do
        let goalTy ← goal.getType
        let proofTy ← inferType proofExpr
        unless ← isDefEq goalTy proofTy do
          throwError "miden_exec_step: summary `{theoremName}` proves{indentExpr (← instantiateMVars proofTy)}\nbut the goal expects{indentExpr (← instantiateMVars goalTy)}"
        goal.assign proofExpr
      pure (← cleanupExecSummaryGoals theoremSideGoals)
  | .nested goal theoremName envExpr fuelExpr stateExpr calleeExpr => do
      let (proofExpr, theoremSideGoals) ←
        buildExecSummaryProofExpr theoremName envExpr fuelExpr stateExpr calleeExpr
      let (rewrittenGoal, rewriteGoals) ← rewriteGoalWithTheorem goal proofExpr
      let theoremRemaining ← cleanupExecSummaryGoals theoremSideGoals
      let mut remaining ← cleanupExecSummaryGoals (theoremRemaining ++ rewriteGoals)
      unless ← rewrittenGoal.isAssigned do
        remaining := remaining ++ (← cleanupGoals [rewrittenGoal])
      pure remaining

/-- Apply a single candidate `_exec` summary theorem to a singleton-exec goal.
    Throws on theorem mismatch or more serious internal failures; callers can
    restore state and try the next candidate on exception. -/
private def applyExecOverrideTheorem
    (goal : MVarId) (parsed : ExecGoal)
    (calleeExpr targetExpr : Lean.Expr) (theoremName : Lean.Name) :
    TacticM (List MVarId) := do
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
  let bridgeRemaining ← cleanupExecBridgeGoals bridgeGoals

  let theoremRemaining ← runExecSummaryStep (.direct callGoal theoremName
      parsed.envExpr directFuelExpr parsed.stateExpr calleeExpr)
  let mut remaining : List MVarId := []
  for g in theoremRemaining ++ bridgeRemaining ++ auxGoals do
    unless ← g.isAssigned do
      remaining := remaining ++ [g]
  pure (← cleanupExecSummaryGoals remaining)

/-- Try to close a singleton `.exec` goal by rewriting it to a direct callee
    execution goal and applying a registered `@[miden_exec_summary]` theorem
    (with parametric-fuel candidates preferred over concrete-fuel ones), or
    falling back to a convention-based `*_exec` theorem. This is the preferred
    path for large callee leaves, with symbolic reflection kept as the
    fallback. -/
private def tryExecOverrideTheoremCore?
    (goal : MVarId) (explicitThm? : Option Lean.Name) :
    TacticM (Option (List MVarId)) := do
  let parsed0 ← parseExecGoal goal
  if !isNatZero parsed0.numLocalsExpr then return none
  let goal ← rewriteZeroLocalsGoalToBody goal
  let parsed ← parseExecGoal goal
  if parsed.opExprs.size != 1 then return none
  let some targetExpr ← execTargetExpr? parsed.opExprs[0]! | return none
  let some calleeExpr ← concreteCalleeExpr? parsed.envExpr targetExpr | return none
  let candidates ← match explicitThm? with
    | some name => pure #[name]
    | none => do
        let mut cs ← registryExecTheoremNames calleeExpr
        if cs.isEmpty then
          if let some name ← execOverrideTheoremName? parsed.envExpr targetExpr then
            cs := cs.push name
        pure cs
  if candidates.isEmpty then return none
  for theoremName in candidates do
    let savedState ← saveState
    try
      return some (← applyExecOverrideTheorem goal parsed calleeExpr targetExpr theoremName)
    catch _ =>
      restoreState savedState
  return none

private def tryExecOverrideTheorem?
    (goal : MVarId) (explicitThm? : Option Lean.Name := none) :
    TacticM (Option (List MVarId)) := do
  -- The core rewrites the goal (assigning the original metavariable) before
  -- several of its `none` early-exits. Restore on `none` so a failed attempt
  -- is side-effect-free — otherwise callers like `miden_reflect` continue
  -- with an already-assigned main goal and fail with an internal-error
  -- `apply` message far from the cause.
  let saved ← saveState
  match ← tryExecOverrideTheoremCore? goal explicitThm? with
  | some remaining => return some remaining
  | none =>
      restoreState saved
      return none

-- ============================================================================
-- miden_exec_step: resolve a single exec call
-- ============================================================================

private inductive ExecStepSite where
  | direct
      (envExpr fuelExpr stateExpr calleeExpr : Lean.Expr)
      (candidates : Array Lean.Name)
  | singleton
      (envExpr fuelExpr stateExpr targetExpr calleeExpr : Lean.Expr)
      (candidates : Array Lean.Name)

private def directExecStepCandidates
    (calleeExpr : Lean.Expr) (explicitThm? : Option Lean.Name) : TacticM (Array Lean.Name) := do
  match explicitThm? with
  | some theoremName => pure #[theoremName]
  | none => registryExecTheoremNames calleeExpr

private def singletonExecStepCandidates
    (envExpr targetExpr calleeExpr : Lean.Expr) (explicitThm? : Option Lean.Name) :
    TacticM (Array Lean.Name) := do
  match explicitThm? with
  | some theoremName => pure #[theoremName]
  | none => do
      let mut candidates ← registryExecTheoremNames calleeExpr
      if candidates.isEmpty then
        if let some theoremName ← execOverrideTheoremName? envExpr targetExpr then
          candidates := candidates.push theoremName
      pure candidates

private def extractProcedureOps? (procExpr : Lean.Expr) : TacticM (Option (Array Lean.Expr)) := do
  if procExpr.isAppOfArity ``MidenLean.Procedure.ofOps 1 then
    return (← extractOps (procExpr.getArg! 0))
  let procWhnf ← whnf procExpr
  if procWhnf.isAppOfArity ``MidenLean.Procedure.ofOps 1 then
    return (← extractOps (procWhnf.getArg! 0))
  if procWhnf.getAppNumArgs == 3 then
    return (← extractOps (procWhnf.getArg! 2))
  return none

/-- Scan a goal for the next theorem-backed exec step. This covers both already
    resolved direct callees and singleton `.exec` calls that still need the
    `execProcedure_singleton_exec_eq` bridge. -/
private partial def findExecStepSiteInExpr
    (e : Lean.Expr) (explicitThm? : Option Lean.Name) :
    TacticM (Option ExecStepSite) := do
  if e.isAppOf ``MidenLean.execProcedure && e.getAppNumArgs >= 4 then
    let envExpr := e.getArg! 0
    let fuelExpr := e.getArg! 1
    let stateExpr := e.getArg! 2
    let procExpr := e.getArg! 3
    if let some procName := procExpr.getAppFn.constName? then
      if procName != ``MidenLean.Procedure.ofOps then
        let candidates ← directExecStepCandidates procExpr explicitThm?
        if !candidates.isEmpty then
          return some (.direct envExpr fuelExpr stateExpr procExpr candidates)
    if let some opExprs ← extractProcedureOps? procExpr then
      if opExprs.size == 1 then
        if let some targetExpr ← execTargetExpr? opExprs[0]! then
          if let some calleeExpr ← concreteCalleeExpr? envExpr targetExpr then
            let candidates ← singletonExecStepCandidates envExpr targetExpr calleeExpr explicitThm?
            if !candidates.isEmpty then
              return some (.singleton envExpr fuelExpr stateExpr targetExpr calleeExpr candidates)
  for i in [:e.getAppNumArgs] do
    if let some result ← findExecStepSiteInExpr (e.getArg! i) explicitThm? then
      return some result
  match e with
  | .lam _ _ body _ => findExecStepSiteInExpr body explicitThm?
  | .letE _ _ value body _ =>
      if let some result ← findExecStepSiteInExpr value explicitThm? then
        return some result
      findExecStepSiteInExpr body explicitThm?
  | .mdata _ body => findExecStepSiteInExpr body explicitThm?
  | _ => return none

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
      -- Hard recursion-depth cap on `ReflectEnv.ofConcrete`. The deepest
      -- caller chain in the core library (rotl → shl → wrapping_mul) is
      -- depth 3, so 8 leaves headroom while preventing the 17-procedure ×
      -- fuel-30 ProcEnv expansion from blowing the kernel stack.
      let maxDepthExpr := Lean.mkNatLit 8
      pure <| some <|
        Lean.mkAppN (Lean.mkConst ``MidenLean.Symbolic.Reflect.ReflectEnv.ofConcrete)
          #[reflectGoal.envExpr, maxDepthExpr, minFuelExpr]
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
    catch ex =>
      throwError "miden_reflect: failed to insert canonical target: {ex.toMessageData}"
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
  runNamedOnGoal "miden_vcg.closeVcgBoolGoal" goal (← `(tactic|
    first
    | assumption
    | decide
    | (split_ifs at * <;> simp_all)
    | simp [miden_reflect_norm,
            MidenLean.Concrete.State.withStack,
            MidenLean.LocalFrame.localAddr,
            and_assoc, and_left_comm, and_comm]
    | tauto
    | omega))

private def canonicalizeVcgGoal
    (goal : MVarId) (closeBridges : Bool := true) : TacticM (MVarId × List MVarId) := do
  let goalTy ← goal.getType
  let some (_, lhs, rhs) := goalTy.eq?
    | pure (goal, [])
  let rhsIsCanonicalTarget :=
    rhs.isMVar || (rhs.isAppOfArity ``Option.some 2 && (rhs.getArg! 1).isMVar)
  if rhsIsCanonicalTarget then
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

/-- Shared front half of the append decomposition used by both `miden_vcg`
    (`decomposeAppendGoalAt`) and `miden_vcg_step`
    (`decomposeAppendGoalAtStep`): rewrite the goal to an explicit
    `prefix ++ suffix` op list, apply `execProcedure_append_eq` with fresh
    intermediate/final state metavariables, and classify the resulting goals
    into `(prefixGoal, suffixGoal, auxGoals, bridgeSeeds)`. When `canonicalize`
    is set, the goal is first rewritten to a canonical `some ?state` target and
    the resulting bridge seeds are returned for the caller to close after
    decomposition (`miden_vcg`); `miden_vcg_step` keeps the goal as-is. -/
private def prepareAppendSplit
    (goal : MVarId) (splitAt : Nat) (tacticName : String) (canonicalize : Bool) :
    TacticM (MVarId × MVarId × List MVarId × List MVarId) := do
  let parsed0 ← parseExecGoal goal
  if !isNatZero parsed0.numLocalsExpr then
    throwError "{tacticName}: control-flow procedures with `numLocals > 0` are not yet supported"
  let goal ← rewriteZeroLocalsGoalToBody goal
  let parsed1 ← parseExecGoal goal
  let prefixExpr ← mkOpListExpr (parsed1.opExprs.toList.take splitAt)
  let suffixExpr ← mkOpListExpr (parsed1.opExprs.toList.drop splitAt)
  let goal ← rewriteGoalToOfOpsAppend goal prefixExpr suffixExpr
  let (goal, bridgeSeeds) ←
    if canonicalize then
      canonicalizeVcgGoal goal (closeBridges := false)
    else
      pure (goal, [])
  let parsed ← parseExecGoal goal
  -- Create the intermediate/final state metavariables in the goal's local
  -- context. Created outside it, they cannot be (checked-)assigned any term
  -- mentioning the goal's free variables, which silently breaks the exec
  -- summary unification downstream.
  let (midStateExpr, finalStateExpr) ← goal.withContext do
    let mid ← mkFreshExprMVar (Lean.mkConst ``MidenLean.Concrete.State)
    let final ← mkFreshExprMVar (Lean.mkConst ``MidenLean.Concrete.State)
    pure (mid, final)
  let theoremExpr := Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure_append_eq)
    #[parsed.envExpr, parsed.fuelExpr, parsed.stateExpr,
      prefixExpr, suffixExpr, midStateExpr, finalStateExpr]
  let goals ←
    try
      goal.apply theoremExpr
    catch ex =>
      let procFmt ← Meta.ppExpr parsed.procExpr
      throwError "{tacticName}: failed to apply append decomposition for {procFmt}: {ex.toMessageData}"
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
        throwError "{tacticName}: append decomposition returned {goals.length} goals: {joined}"
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
      throwError "{tacticName}: could not classify append decomposition goals"
  pure (prefixGoal, suffixGoal, auxGoals, bridgeSeeds)

/-- Shared core of the fast `ifElse` split used by both `miden_vcg`
    (`splitIfElseFastGoal`) and `miden_vcg_step` (`splitIfElseFastGoalStep`):
    case-split on the branch condition, discharge each side's `ite` residue,
    classify the two surviving `execProcedure` goals into then/else, and clean
    up the administrative rest. Returns `(thenGoal, elseGoal, auxRemaining)`.

    The branch-discharge ladder below was chosen empirically over the whole
    proof suite: the tactics previously diverged (`simp [h]` for `miden_vcg`,
    `split_ifs`/`simp_all` for `miden_vcg_step`), and the `simp [h]` variant
    fails on step-style chunked proofs (U128 `shl`), while this one passes
    everywhere at a ~1s/module elaboration cost on ifElse-heavy proofs. -/
private def prepareIfElseFastSplit
    (goal : MVarId) (propExpr : Lean.Expr) (thenOps elseOps : Lean.Expr)
    (tacticName : String) :
    TacticM (MVarId × MVarId × List MVarId) := do
  let (posGoal, negGoal) ← goal.byCases propExpr `h
  let discharge (g : MVarId) (label : String) : TacticM (List MVarId) := do
    try
      runTacticSeqOnGoal g (← `(tacticSeq|
        try (split_ifs at *)
        simp_all))
    catch ex =>
      let ty ← g.getType
      throwError "{tacticName}.splitIfElseFast.{label} failed on goal:{indentExpr ty}\n{ex.toMessageData}"
  let posGoals ← discharge posGoal.mvarId "true"
  let negGoals ← discharge negGoal.mvarId "false"
  let splitGoals := posGoals ++ negGoals
  let mut execGoals : List MVarId := []
  let mut auxGoals : List MVarId := []
  for g in splitGoals do
    unless ← g.isAssigned do
      let ty ← g.getType
      match ty.eq? with
      | some (_, lhs, _) =>
          if lhs.isAppOf ``MidenLean.execProcedure then
            execGoals := execGoals ++ [g]
          else
            auxGoals := auxGoals ++ [g]
      | none =>
          auxGoals := auxGoals ++ [g]
  let [execGoal1, execGoal2] := execGoals
    | do
        let goalTypes ← splitGoals.mapM (fun g => do
          let fmt ← Meta.ppExpr (← g.getType)
          pure <| MessageData.ofFormat fmt)
        let joined := MessageData.joinSep goalTypes " | "
        throwError "{tacticName}: expected two execution goals after fast `ifElse` split, got {execGoals.length}: {joined}"
  let goal1IsThen ← branchBodyMatches execGoal1 thenOps
  let goal1IsElse ← branchBodyMatches execGoal1 elseOps
  let goal2IsThen ← branchBodyMatches execGoal2 thenOps
  let goal2IsElse ← branchBodyMatches execGoal2 elseOps
  let (thenGoal, elseGoal) ←
    if goal1IsThen && goal2IsElse then
      pure (execGoal1, execGoal2)
    else if goal1IsElse && goal2IsThen then
      pure (execGoal2, execGoal1)
    else
      throwError "{tacticName}: could not classify fast `ifElse` branch goals"
  let auxRemaining ← cleanupGoals auxGoals
  pure (thenGoal, elseGoal, auxRemaining)

/-- Classify `ifElse` subgoals into hs, hfuel, branch (forall), hbool (Or), and aux goals. -/
private def classifyIfElseGoals (goals : List MVarId) :
    TacticM (MVarId × MVarId × List MVarId × MVarId × List MVarId) := do
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
  let some hboolGoal := hboolGoal? | throwError "miden_vcg: missing `hbool` goal for singleton `ifElse`"
  pure (hsGoal, hfuelGoal, branchGoals, hboolGoal, auxGoals)

private def closeIfElseFastRewriteGoals (goals : List MVarId) : TacticM (List MVarId) := do
  let mut remaining : List MVarId := []
  for g in goals do
    unless ← g.isAssigned do
      let ty ← g.getType
      if ty.eq?.isSome then
        if ← closeEqByAssigningMVar? g then
          pure ()
        else
          let rem ← runNamedOnGoal "miden_vcg.closeIfElseFastRewriteGoals.eq" g (← `(tactic|
            first
            | assumption
            | symm; assumption
            | rfl
            | simp [MidenLean.Concrete.State.withStack]))
          for remGoal in rem do
            unless ← remGoal.isAssigned do
              if ← closeEqByAssigningMVar? remGoal then
                pure ()
              else
                remaining := remaining ++ [remGoal]
      else
        let rem ← runNamedOnGoal "miden_vcg.closeIfElseFastRewriteGoals.prop" g (← `(tactic|
          first
          | omega
          | assumption
          | decide
          | simp))
        remaining := remaining ++ rem
  cleanupGoals remaining

/-- Shared core of the fast singleton `ifElse` decomposition used by both
    `miden_vcg` (`tryDecomposeIfElseFast`) and `miden_vcg_step`
    (`tryDecomposeIfElseFastStep`): enumerate fast rewrite theorem candidates
    for the branch condition and attempt each in turn — insert an `Eq.trans`
    bridge with a fresh middle metavariable, apply the candidate theorem to the
    execution side, and discharge the rewrite side goals. On success returns
    `(theoremRemaining, bridgeGoal, splitProp?)`; the caller finishes the
    bridge goal (recursively for `miden_vcg`, single-step for
    `miden_vcg_step`), case-splitting on `splitProp?` when present.

    Candidates, in order: constant `1`/`0` conditions (after reduction), then
    `ite`/`dite` conditions with a synthesized `Decidable` instance, trying the
    positive theorem before the negative one. The `ite`/`dite` condition is
    read from the syntactic condition first (the historical `miden_vcg_step`
    behavior, `tryApplyFastIfElseTheoremStep?`) and from the reduced condition
    as a fallback (the historical `miden_vcg` behavior); the `dite` and
    try-both-polarities paths were originally step-only and are now available
    to both tactics. -/
private def prepareIfElseFastDecompose
    (goal : MVarId) (thenOps elseOps : Lean.Expr) (tacticName : String) :
    TacticM (Option (List MVarId × MVarId × Option Lean.Expr)) := do
  let parsed ← parseExecGoal goal
  let (stackElems, tailExpr) ← getStateStackDecomposition parsed.stateExpr
  if stackElems.isEmpty then
    return none
  let condExpr := stackElems[0]!
  let restExpr ← mkListExprWithTail (stackElems.toList.drop 1) tailExpr
  let zeroExpr ← Lean.Elab.Term.elabTerm (← `((0 : MidenLean.Felt))) none
  let oneExpr ← Lean.Elab.Term.elabTerm (← `((1 : MidenLean.Felt))) none
  let condInst ← instantiateMVars condExpr
  let condWhnf ← withTransparency TransparencyMode.all <| reduce condInst
  let baseArgs := #[parsed.envExpr, parsed.fuelExpr, parsed.stateExpr, restExpr, thenOps, elseOps]
  let mut candidates : List (Lean.Expr × Option Lean.Expr) := []
  if ← isDefEq condWhnf oneExpr then
    candidates := candidates ++
      [(Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure_ifElse_state_one) baseArgs, none)]
  if ← isDefEq condWhnf zeroExpr then
    candidates := candidates ++
      [(Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure_ifElse_state_zero) baseArgs, none)]
  let iteProp? (e : Lean.Expr) : Option Lean.Expr :=
    if (e.isAppOf ``ite || e.isAppOf ``dite) && e.getAppNumArgs = 5 then
      some (e.getArg! 1)
    else
      none
  let mut propExprs : List Lean.Expr := []
  if let some p := iteProp? condInst then
    propExprs := propExprs ++ [p]
  if let some p := iteProp? condWhnf then
    unless propExprs.contains p do
      propExprs := propExprs ++ [p]
  for propExpr in propExprs do
    try
      let decInst ← synthInstance (Lean.mkApp (Lean.mkConst ``Decidable) propExpr)
      let iteArgs := (baseArgs.push propExpr).push decInst
      candidates := candidates ++
        [(Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure_ifElse_bool_ite) iteArgs,
            some propExpr),
          (Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure_ifElse_bool_ite_neg) iteArgs,
            some propExpr)]
    catch _ =>
      pure ()
  for (theoremExpr, splitProp?) in candidates do
    let savedState ← saveState
    try
      let eqTransExpr ← goal.withContext do
        let targetTy ← inferType parsed.lhs
        let middleExpr ← mkFreshExprMVar targetTy
        mkAppOptM ``Eq.trans
          #[some targetTy, some parsed.lhs, some middleExpr, some parsed.rhs]
      let splitGoals ← goal.apply eqTransExpr
      let mut execGoal? : Option MVarId := none
      let mut bridgeGoal? : Option MVarId := none
      let mut auxGoals : List MVarId := []
      for g in splitGoals do
        unless ← g.isAssigned do
          let ty ← g.getType
          match ty.eq? with
          | some (_, lhs, _) =>
              if lhs.isAppOf ``MidenLean.execProcedure then
                execGoal? := some g
              else
                bridgeGoal? := some g
          | none =>
              auxGoals := auxGoals ++ [g]
      let some theoremGoal := execGoal?
        | throwError "{tacticName}: missing execution goal for fast `ifElse` decomposition"
      let some bridgeGoal := bridgeGoal?
        | throwError "{tacticName}: missing bridge goal for fast `ifElse` decomposition"
      let theoremGoals ← theoremGoal.apply theoremExpr
      let theoremRemaining ← closeIfElseFastRewriteGoals (theoremGoals ++ auxGoals)
      return some (theoremRemaining, bridgeGoal, splitProp?)
    catch _ =>
      restoreState savedState
  return none

/-- Shared core of the slow singleton `ifElse` decomposition used by both
    `miden_vcg` (`decomposeIfElse`) and `miden_vcg_step`
    (`decomposeIfElseStep`): apply `execProcedure_ifElse` (ite form, tried
    first), falling back to `execProcedure_ifElse_same` (same-output form),
    close the stack and fuel side goals, and classify the two introduced
    branch goals into then/else. Returns
    `(thenBodyGoal, elseBodyGoal, hboolGoal, auxGoals)`; the caller recurses
    into the branch bodies (`miden_vcg`) or returns them (`miden_vcg_step`)
    and closes the bool/aux goals. -/
private def prepareIfElseSlowSplit
    (goal : MVarId) (thenOps elseOps : Lean.Expr) (tacticName : String) :
    TacticM (MVarId × MVarId × MVarId × List MVarId) := do
  let parsed ← parseExecGoal goal
  let condExpr ← mkFreshExprMVar (Lean.mkConst ``MidenLean.Felt)
  let restExpr ← mkFreshExprMVar
    (Lean.mkApp (Lean.mkConst ``List [Lean.levelZero]) (Lean.mkConst ``MidenLean.Felt))
  -- Try the ite form first (produces `if cond.val = 1 then s_then else s_else`)
  let savedState ← saveState
  let goals ← do
    let sThenExpr ← mkFreshExprMVar (Lean.mkConst ``MidenLean.Concrete.State)
    let sElseExpr ← mkFreshExprMVar (Lean.mkConst ``MidenLean.Concrete.State)
    let theoremExpr := Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure_ifElse)
      #[parsed.envExpr, parsed.fuelExpr, thenOps, elseOps,
        parsed.stateExpr, sThenExpr, sElseExpr, condExpr, restExpr]
    try
      goal.apply theoremExpr
    catch _ =>
      restoreState savedState
      -- Fallback: same-output form (both branches produce the same state)
      let sExpr ← mkFreshExprMVar (Lean.mkConst ``MidenLean.Concrete.State)
      let theoremExpr := Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure_ifElse_same)
        #[parsed.envExpr, parsed.fuelExpr, thenOps, elseOps,
          parsed.stateExpr, sExpr, condExpr, restExpr]
      try
        goal.apply theoremExpr
      catch ex =>
        throwError "{tacticName}: failed to decompose singleton `ifElse`: {ex.toMessageData}"
  let (hsGoal, hfuelGoal, branchGoals, hboolGoal, auxGoals) ← classifyIfElseGoals goals
  let [branchGoal1, branchGoal2] := branchGoals
    | throwError "{tacticName}: expected two branch goals for singleton `ifElse`, got {branchGoals.length}"
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
      throwError "{tacticName}: could not classify singleton `ifElse` branch goals"
  pure (hthenBodyGoal, helseBodyGoal, hboolGoal, auxGoals)

/-- Result of the shared singleton-`repeat` decomposition front. -/
private inductive RepeatSplit where
  /-- `repeat 0`: the goal rewritten past the empty iteration, plus residual
      non-`Prop` side goals from the rewrite. -/
  | zero (goal : MVarId) (otherGoals : List MVarId)
  /-- `repeat (n+1)`: the classified body/rest execution goals plus aux goals.
      The `hfuel` side goal is already closed. -/
  | succ (bodyGoal restGoal : MVarId) (auxGoals : List MVarId)

/-- Shared front half of the singleton `repeat` decomposition used by both
    `miden_vcg` (the `.repeat` case of `decomposeVcgGoal`) and `miden_vcg_step`
    (`decomposeRepeatStep`): for count 0, rewrite with
    `execProcedure_repeat_zero` and close the fuel side goals; for count > 0,
    apply `execProcedure_repeat_succ`, classify the goals into
    hfuel/body/rest/aux, and close the fuel goal. The recurse-vs-return tail
    stays with the caller. -/
private def prepareRepeatSplit
    (goal : MVarId) (countExpr bodyOps : Lean.Expr) (tacticName : String) :
    TacticM RepeatSplit := do
  let parsed ← parseExecGoal goal
  let some count := countExpr.numeral?
    | throwError "{tacticName}: `repeat` count must reduce to a Nat literal"
  if count = 0 then
    let theoremExpr := Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure_repeat_zero)
      #[parsed.envExpr, parsed.fuelExpr, bodyOps, parsed.stateExpr]
    let rwResult ←
      try
        goal.rewrite (← goal.getType) theoremExpr
      catch ex =>
        throwError "{tacticName}: failed to decompose singleton `repeat 0`: {ex.toMessageData}"
    let goal' ← goal.replaceTargetEq rwResult.eNew rwResult.eqProof
    let mut otherGoals : List MVarId := []
    for g in rwResult.mvarIds do
      unless ← g.isAssigned do
        let ty ← g.getType
        if ← isProp ty then
          closeVcgFuelGoal g
        else
          otherGoals := otherGoals ++ [g]
    return .zero goal' otherGoals
  else
    let theoremExpr := Lean.mkAppN (Lean.mkConst ``MidenLean.execProcedure_repeat_succ)
      #[parsed.envExpr, parsed.fuelExpr, Lean.mkNatLit (count - 1), bodyOps]
    let goals ←
      try
        goal.apply theoremExpr
      catch ex =>
        throwError "{tacticName}: failed to decompose singleton `repeat`: {ex.toMessageData}"
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
    let some hfuelGoal := hfuelGoal?
      | throwError "{tacticName}: missing `hfuel` goal for singleton `repeat`"
    let [execGoal1, execGoal2] := execGoals
      | throwError "{tacticName}: expected two execution goals for singleton `repeat`, got {execGoals.length}"
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
        throwError "{tacticName}: could not classify singleton `repeat` goals"
    closeVcgFuelGoal hfuelGoal
    return .succ bodyGoal restGoal auxGoals

mutual

private partial def decomposeAppendGoalAt (goal : MVarId) (splitAt : Nat) : TacticM (List MVarId) := do
  let (prefixGoal, suffixGoal, auxGoals, bridgeSeeds) ←
    prepareAppendSplit goal splitAt "miden_vcg" (canonicalize := true)
  let prefixRemaining ← decomposeVcgGoal prefixGoal
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  -- Eagerly close bridge goals from the prefix (especially the repeat base
  -- case `some ?s₄ = some ?midState`) so that the intermediate state metavar
  -- is assigned before the suffix's `miden_reflect` can mis-unify it with the
  -- original state via the `hs` hypothesis.
  let mut prefixBridges : List MVarId := []
  let mut prefixOther : List MVarId := []
  for g in prefixRemaining do
    unless ← g.isAssigned do
      let ty ← g.getType
      if ty.eq?.isSome then
        prefixBridges := prefixBridges ++ [g]
      else
        prefixOther := prefixOther ++ [g]
  let mut prefixBridgeRemaining : List MVarId := []
  for g in prefixBridges do
    prefixBridgeRemaining := prefixBridgeRemaining ++ (← closeBridgeGoal g)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let suffixRemaining ← decomposeVcgGoal suffixGoal
  let auxRemaining ← cleanupGoals auxGoals
  let bridgeRemaining ← cleanupGoals bridgeSeeds
  return prefixOther ++ prefixBridgeRemaining ++ suffixRemaining ++ auxRemaining ++ bridgeRemaining

private partial def splitIfElseFastGoal
    (goal : MVarId) (propExpr : Lean.Expr) (thenOps elseOps : Lean.Expr) : TacticM (List MVarId) := do
  let (thenGoal, elseGoal, auxRemaining) ←
    prepareIfElseFastSplit goal propExpr thenOps elseOps "miden_vcg"
  let thenRemaining ← decomposeVcgGoal thenGoal
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let elseRemaining ← decomposeVcgGoal elseGoal
  pure (thenRemaining ++ elseRemaining ++ auxRemaining)

private partial def tryDecomposeIfElseFast
    (goal : MVarId) (thenOps elseOps : Lean.Expr) : TacticM (Option (List MVarId)) := do
  let (goal, bridgeSeeds) ← canonicalizeVcgGoal goal (closeBridges := false)
  let some (theoremRemaining, bridgeGoal, splitProp?) ←
      prepareIfElseFastDecompose goal thenOps elseOps "miden_vcg"
    | return none
  let branchRemaining ←
    match splitProp? with
    | some propExpr => splitIfElseFastGoal bridgeGoal propExpr thenOps elseOps
    | none => decomposeVcgGoal bridgeGoal
  let mut bridgePending : List MVarId := []
  for g in bridgeSeeds do
    bridgePending := bridgePending ++ (← closeBridgeGoal g)
  let bridgeRemaining ← cleanupGoals bridgePending
  pure (some (theoremRemaining ++ branchRemaining ++ bridgeRemaining))

/-- Decompose a singleton `ifElse` using `execProcedure_ifElse` (ite form)
    or `execProcedure_ifElse_same` (same-output form).

    The ite form is tried first; it succeeds when the goal RHS already contains
    a state-level `if`. When both branches produce the same output state and
    the goal RHS is a single state (no `if`), the same-output form is used as
    a fallback. -/
private partial def decomposeIfElse
    (goal : MVarId) (thenOps elseOps : Lean.Expr) : TacticM (List MVarId) := do
  let savedFastState ← saveState
  match ← tryDecomposeIfElseFast goal thenOps elseOps with
  | some remaining => return remaining
  | none => restoreState savedFastState
  let (goal, bridgeSeeds) ← canonicalizeVcgGoal goal (closeBridges := false)
  let (hthenBodyGoal, helseBodyGoal, hboolGoal, auxGoals) ←
    prepareIfElseSlowSplit goal thenOps elseOps "miden_vcg"
  let thenRemaining ← decomposeVcgGoal hthenBodyGoal
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let elseRemaining ← decomposeVcgGoal helseBodyGoal
  let boolRemaining ← closeVcgBoolGoal hboolGoal
  let auxRemaining ← cleanupGoals auxGoals
  let mut bridgePending : List MVarId := []
  for g in bridgeSeeds do
    bridgePending := bridgePending ++ (← closeBridgeGoal g)
  let bridgeRemaining ← cleanupGoals bridgePending
  return thenRemaining ++ elseRemaining ++ boolRemaining ++ auxRemaining ++ bridgeRemaining

private partial def decomposeVcgGoal (goal : MVarId) : TacticM (List MVarId) := do
  if ← goal.isAssigned then
    pure []
  else
    let parsed0 ← parseExecGoal goal
    let noControl := (← firstControlBoundary? parsed0.opExprs).isNone
    if noControl then
      if !isNatZero parsed0.numLocalsExpr then
        return ← runNamedOnGoal "miden_vcg.reflectLeaf.locals" goal (← `(tactic| miden_reflect))
      let goal ← rewriteZeroLocalsGoalToBody goal
      let parsed ← parseExecGoal goal
      if let some splitAt ← firstExecSplitIndex? parsed.opExprs then
        return ← decomposeAppendGoalAt goal splitAt
      else
        if let some rem ← tryExecOverrideTheorem? goal then
          return rem
        return ← runNamedOnGoal "miden_vcg.reflectLeaf" goal (← `(tactic| miden_reflect))

    if !isNatZero parsed0.numLocalsExpr then
      throwError "miden_vcg: control-flow procedures with `numLocals > 0` are not yet supported"

    let goal ← rewriteZeroLocalsGoalToBody goal
    let parsed ← parseExecGoal goal
    let some (idx, boundary) ← firstControlBoundary? parsed.opExprs
      | do
          if let some rem ← tryExecOverrideTheorem? goal then
            return rem
          return ← runOnGoal goal (← `(tactic| miden_reflect))

    if parsed.opExprs.size > 1 then
      return ← decomposeAppendGoalAt goal (if idx = 0 then 1 else idx)

    match boundary with
    | .ifElse thenOps elseOps =>
        decomposeIfElse goal thenOps elseOps
    | .repeat countExpr bodyOps =>
        match ← prepareRepeatSplit goal countExpr bodyOps "miden_vcg" with
        | .zero goal' otherGoals =>
            -- Close the bridge goal eagerly so intermediate state metavars are
            -- assigned before downstream goals (e.g. suffix after append split)
            -- can mis-unify them with the original state.
            let bridgeRemaining ← closeBridgeGoal goal'
            cleanupGoals (bridgeRemaining ++ otherGoals)
        | .succ bodyGoal restGoal auxGoals =>
            let bodyRemaining ← decomposeVcgGoal bodyGoal
            Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
            let restRemaining ← decomposeVcgGoal restGoal
            let auxRemaining ← cleanupGoals auxGoals
            return bodyRemaining ++ restRemaining ++ auxRemaining
    | .whileTrue _ =>
        throwError "miden_vcg: `whileTrue` is not yet supported. Use manual proofs with invariants."

end

mutual

private partial def decomposeAppendGoalAtStep (goal : MVarId) (splitAt : Nat) : TacticM (List MVarId) := do
  let (prefixGoal, suffixGoal, auxGoals, _) ←
    prepareAppendSplit goal splitAt "miden_vcg_step" (canonicalize := false)
  let auxRemaining ← cleanupGoals auxGoals
  let mut remaining : List MVarId := []
  unless ← prefixGoal.isAssigned do
    remaining := remaining ++ [prefixGoal]
  unless ← suffixGoal.isAssigned do
    remaining := remaining ++ [suffixGoal]
  return remaining ++ auxRemaining

private partial def splitIfElseFastGoalStep
    (goal : MVarId) (propExpr : Lean.Expr) (thenOps elseOps : Lean.Expr) : TacticM (List MVarId) := do
  let (thenGoal, elseGoal, auxRemaining) ←
    prepareIfElseFastSplit goal propExpr thenOps elseOps "miden_vcg_step"
  let mut remaining : List MVarId := []
  unless ← thenGoal.isAssigned do
    remaining := remaining ++ [thenGoal]
  unless ← elseGoal.isAssigned do
    remaining := remaining ++ [elseGoal]
  return remaining ++ auxRemaining

private partial def tryDecomposeIfElseFastStep
    (goal : MVarId) (thenOps elseOps : Lean.Expr) : TacticM (Option (List MVarId)) := do
  let some (theoremRemaining, bridgeGoal, splitProp?) ←
      prepareIfElseFastDecompose goal thenOps elseOps "miden_vcg_step"
    | return none
  let branchRemaining ←
    match splitProp? with
    | some propExpr => splitIfElseFastGoalStep bridgeGoal propExpr thenOps elseOps
    | none =>
        if ← bridgeGoal.isAssigned then
          pure []
        else
          pure [bridgeGoal]
  pure (some (theoremRemaining ++ branchRemaining))

private partial def decomposeIfElseStep
    (goal : MVarId) (thenOps elseOps : Lean.Expr) : TacticM (List MVarId) := do
  let savedFastState ← saveState
  match ← tryDecomposeIfElseFastStep goal thenOps elseOps with
  | some remaining => return remaining
  | none => restoreState savedFastState
  let (hthenBodyGoal, helseBodyGoal, hboolGoal, auxGoals) ←
    prepareIfElseSlowSplit goal thenOps elseOps "miden_vcg_step"
  let boolRemaining ← closeVcgBoolGoal hboolGoal
  let auxRemaining ← cleanupGoals auxGoals
  let mut remaining : List MVarId := []
  unless ← hthenBodyGoal.isAssigned do
    remaining := remaining ++ [hthenBodyGoal]
  unless ← helseBodyGoal.isAssigned do
    remaining := remaining ++ [helseBodyGoal]
  return remaining ++ boolRemaining ++ auxRemaining

private partial def decomposeRepeatStep
    (goal : MVarId) (countExpr bodyOps : Lean.Expr) : TacticM (List MVarId) := do
  match ← prepareRepeatSplit goal countExpr bodyOps "miden_vcg_step" with
  | .zero goal' otherGoals =>
      let mut remaining : List MVarId := []
      unless ← goal'.isAssigned do
        remaining := remaining ++ [goal']
      let otherRemaining ← cleanupGoals otherGoals
      return remaining ++ otherRemaining
  | .succ bodyGoal restGoal auxGoals =>
      let auxRemaining ← cleanupGoals auxGoals
      let mut remaining : List MVarId := []
      unless ← bodyGoal.isAssigned do
        remaining := remaining ++ [bodyGoal]
      unless ← restGoal.isAssigned do
        remaining := remaining ++ [restGoal]
      return remaining ++ auxRemaining

private partial def decomposeVcgStepGoal (goal : MVarId) : TacticM (List MVarId) := do
  if ← goal.isAssigned then
    pure []
  else
    let parsed0 ← parseExecGoal goal
    let noControl := (← firstControlBoundary? parsed0.opExprs).isNone
    if noControl then
      if !isNatZero parsed0.numLocalsExpr then
        return [goal]
      let goal ← rewriteZeroLocalsGoalToBody goal
      let parsed ← parseExecGoal goal
      if let some splitAt ← firstExecSplitIndex? parsed.opExprs then
        return ← decomposeAppendGoalAtStep goal splitAt
      else
        return [goal]

    if !isNatZero parsed0.numLocalsExpr then
      throwError "miden_vcg_step: control-flow procedures with `numLocals > 0` are not yet supported"

    let goal ← rewriteZeroLocalsGoalToBody goal
    let parsed ← parseExecGoal goal
    let some (idx, boundary) ← firstControlBoundary? parsed.opExprs
      | return [goal]

    if parsed.opExprs.size > 1 then
      return ← decomposeAppendGoalAtStep goal (if idx = 0 then 1 else idx)

    match boundary with
    | .ifElse thenOps elseOps =>
        decomposeIfElseStep goal thenOps elseOps
    | .repeat countExpr bodyOps =>
        decomposeRepeatStep goal countExpr bodyOps
    | .whileTrue _ =>
        throwError "miden_vcg_step: `whileTrue` is not yet supported. Use manual proofs with invariants."

end

/-- Result of attempting a nested theorem-backed exec step. -/
private inductive NestedExecStepResult where
  | notFound
  | success (remaining : List MVarId)
  | failed (msg : MessageData)

private def tryNestedExecStep
    (goal : MVarId) (explicitThm? : Option Lean.Name := none) :
    TacticM NestedExecStepResult := do
  let goalTy ← goal.getType
  let some site ← findExecStepSiteInExpr goalTy explicitThm?
    | return .notFound
  let candidates := match site with
    | .direct _ _ _ _ cs => cs
    | .singleton _ _ _ _ _ cs => cs
  let mut lastErr? : Option MessageData := none
  for theoremName in candidates do
    let savedState ← saveState
    try
      let (goalAfterBridge, bridgeSideGoals, directSite) ←
        match site with
        | .direct envExpr fuelExpr stateExpr calleeExpr _ =>
            pure (goal, ([] : List MVarId), (envExpr, fuelExpr, stateExpr, calleeExpr))
        | .singleton envExpr fuelExpr stateExpr targetExpr calleeExpr _ => do
            let (goal', bridgeGoals) ←
              rewriteGoalWithSingletonExecBridge goal envExpr fuelExpr stateExpr targetExpr calleeExpr
            let bridgeRemaining ← cleanupExecBridgeGoals bridgeGoals
            let goalTy' ← goal'.getType
            let some (.direct envExpr' fuelExpr' stateExpr' calleeExpr' _)
                ← findExecStepSiteInExpr goalTy' (some theoremName)
              | throwError "miden_exec_step: failed to expose the direct callee after bridging"
            pure (goal', bridgeRemaining, (envExpr', fuelExpr', stateExpr', calleeExpr'))
      let (envExpr, fuelExpr, stateExpr, calleeExpr) := directSite
      let remaining ← runExecSummaryStep (.nested goalAfterBridge theoremName
          envExpr fuelExpr stateExpr calleeExpr)
      return .success (bridgeSideGoals ++ remaining)
    catch ex =>
      restoreState savedState
      lastErr? := some m!"candidate `{theoremName}` failed: {ex.toMessageData}"
  return .failed (lastErr?.getD
    m!"found a theorem-backed exec site, but summary application and cleanup failed")

/-- Core implementation for `miden_exec_step`. Tries two strategies:

    **Strategy A** — the goal is a top-level `execProcedure` equation with a
    singleton `.exec` op. Resolves the `ProcEnv` lookup, applies
    `execProcedure_singleton_exec_eq`, applies the callee theorem, and closes
    mechanical side-goals.

    **Strategy B** — the next exec is nested under the goal (typically inside a
    `bind` chain after `execProcedure_append`). If the callee is already
    visible, rewrite directly; if the goal still contains a singleton
    `[.exec "..."]`, insert `execProcedure_singleton_exec_eq` first, then apply
    the callee theorem and pass the rewritten goal back through the shared VCG
    decomposition / leaf solver. -/
private def execStepImpl (thmId? : Option (TSyntax `ident)) : TacticM Unit := do
  let mainGoal ← getMainGoal
  let explicitName? : Option Lean.Name := thmId?.map (·.getId)

  let saved ← saveState
  try
    if let some remaining ← tryExecOverrideTheorem? mainGoal explicitName? then
      setGoals remaining
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      return
  catch _ => pure ()
  restoreState saved

  let saved ← saveState
  match ← tryNestedExecStep mainGoal explicitName? with
  | .success remaining =>
      setGoals remaining
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  | .failed msg =>
      restoreState saved
      throwError "miden_exec_step: found theorem-backed exec site but could not resolve it: {msg}"
  | .notFound =>
      restoreState saved
      throwError "miden_exec_step: no theorem-backed exec call found in goal. \
        Expose the next `execProcedure` call with `execProcedure_append`, or use \
        `miden_exec_step [thm]` to provide the callee theorem explicitly."

/-- `miden_exec_step` resolves a single theorem-backed exec call in the goal.

    When the goal is a top-level singleton `.exec`, the tactic reuses the same
    summary-application path as `miden_reflect`.

    When the next exec is nested under a larger goal, the tactic bridges to the
    direct callee if needed, rewrites with the shared summary engine, and then
    hands the residual execution goal back to the normal VCG decomposition /
    leaf solver so simple suffixes can close automatically.

    Usage:
      miden_exec_step              -- automatic `@[miden_exec_summary]` lookup
      miden_exec_step [thm_name]   -- explicit theorem -/
syntax "miden_exec_step" : tactic
syntax "miden_exec_step" "[" ident "]" : tactic

elab_rules : tactic
  | `(tactic| miden_exec_step) => execStepImpl none
  | `(tactic| miden_exec_step [ $thmId:ident ]) => execStepImpl (some thmId)

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

/-- `miden_vcg_step` performs one structural VCG decomposition step, closing
    only administrative side goals and leaving the resulting execution goals
    for the user or for subsequent tactics. Supported control flow:
    `ifElse` and concrete-count `repeat`. `whileTrue` remains unsupported. -/
syntax "miden_vcg_step" : tactic
elab_rules : tactic
  | `(tactic| miden_vcg_step) => do
      let mainGoal ← getMainGoal
      let remaining ← decomposeVcgStepGoal mainGoal
      setGoals remaining
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing

end MidenLean.Symbolic.Tactic
