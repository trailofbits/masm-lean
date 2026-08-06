import MidenLean.Proofs.ControlFlow
import MidenLean.Symbolic.Tactic

/-!
# Control Flow Tests

Validation tests for the control-flow composition rules (Phase 4).
Tests 1–3 apply the composition rules directly; Test 4 uses the `miden_vcg`
tactic for `ifElse`; Test 5 applies `execProcedure_while` with an explicit
invariant and measure.
-/

namespace MidenLean.ControlFlowTest

open MidenLean

-- ============================================================================
-- Test 1: ifElse — singleton ifElse op
-- ============================================================================

/-- Direct test of execProcedure_ifElse: if cond=1 then add 10, else add 20.
    Uses concrete fuel = 2 so branch bodies can unfold. -/
theorem ifElse_test
    (env : ProcEnv) (cond x : Felt)
    (rest : List Felt) (mem : Nat → Felt)
    (frames : List LocalFrame) (adv : List Felt)
    (hbool : cond.val = 0 ∨ cond.val = 1) :
    execProcedure env 2
      ⟨cond :: x :: rest, mem, frames, adv⟩
      (Procedure.ofOps [Op.ifElse
        [Op.inst (.push 10), Op.inst .add]
        [Op.inst (.push 20), Op.inst .add]]) =
      some (if cond.val = 1
        then (⟨cond :: x :: rest, mem, frames, adv⟩ : Concrete.State).withStack ((x + 10) :: rest)
        else (⟨cond :: x :: rest, mem, frames, adv⟩ : Concrete.State).withStack ((x + 20) :: rest)) := by
  apply execProcedure_ifElse env 2 _ _ _ _ _ cond (x :: rest) rfl (by omega)
  · intro h1
    simp [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind,
          MidenLean.execInstruction, execPush, execAdd, Concrete.State.withStack]
  · intro h0
    simp [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind,
          MidenLean.execInstruction, execPush, execAdd, Concrete.State.withStack]
  · exact hbool

-- ============================================================================
-- Test 2: repeat with invariant — push 1 three times
-- ============================================================================

/-- Test execProcedure_repeat_succ + execProcedure_repeat_zero: repeat.3 { push 1 }.
    Input: [rest...], Output: [1, 1, 1, rest...] -/
theorem repeat_test
    (env : ProcEnv) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execProcedure env 2 ⟨rest, mem, frames, adv⟩ [Op.repeat 3 (body := [Op.inst (.push 1)])] =
    some ⟨1 :: 1 :: 1 :: rest, mem, frames, adv⟩ := by
  apply execProcedure_repeat_succ env 2 2 _ _ ⟨1 :: rest, mem, frames, adv⟩ _ (by omega)
  · simp [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind,
          MidenLean.execInstruction, execPush, Concrete.State.withStack]
  apply execProcedure_repeat_succ env 2 1 _ _ ⟨1 :: 1 :: rest, mem, frames, adv⟩ _ (by omega)
  · simp [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind,
          MidenLean.execInstruction, execPush, Concrete.State.withStack]
  apply execProcedure_repeat_succ env 2 0 _ _ ⟨1 :: 1 :: 1 :: rest, mem, frames, adv⟩ _ (by omega)
  · simp [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind,
          MidenLean.execInstruction, execPush, Concrete.State.withStack]
  exact execProcedure_repeat_zero env 2 _ _ (by omega)

-- ============================================================================
-- Test 3: whileTrue — body pushes 0, loop exits after 1 iteration
-- ============================================================================

/-- Test doWhile: body = push 0.
    Input:  [1, rest...] (condition = 1, loop enters)
    After body: [0, rest...] (condition = 0, loop exits)
    Output: [rest...] -/
theorem while_test
    (env : ProcEnv) (fuel : Nat)
    (rest : List Felt) (mem : Nat → Felt)
    (frames : List LocalFrame) (adv : List Felt)
    (hfuel : fuel ≥ 2) :
    ∃ s', execProcedure.doWhile env fuel fuel
      [Op.inst (.push 0)]
      ⟨(1 : Felt) :: rest, mem, frames, adv⟩ = some s'
      ∧ s'.stack = rest := by
  obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 2 := ⟨fuel - 2, by omega⟩
  have h1v : (1 : Felt).val = 1 :=
    felt_ofNat_val_lt 1 (by unfold GOLDILOCKS_PRIME; omega)
  have h0v : (0 : Felt).val = 0 :=
    felt_ofNat_val_lt 0 (by unfold GOLDILOCKS_PRIME; omega)
  -- Provide witness and prove execution
  refine ⟨⟨rest, mem, frames, adv⟩, ?_, rfl⟩
  simp [execProcedure.doWhile, execProcedure, Procedure.ofOps, List.foldlM,
        bind, Bind.bind, Option.bind,
        MidenLean.execInstruction, execPush, Concrete.State.withStack,
        h1v, h0v]

-- ============================================================================
-- Test 4: ifElse via miden_vcg — tactic auto-applies execProcedure_ifElse
-- ============================================================================

/-- Validates miden_vcg on a singleton ifElse procedure.
    The tactic decomposes the control flow; residual goals are closed by
    `miden_finish_reflection`. -/
theorem ifElse_vcg_test
    (env : ProcEnv) (cond x : Felt)
    (rest : List Felt) (s : Concrete.State)
    (hs : s = ⟨cond :: x :: rest, fun _ => 0, [], []⟩)
    (hbool : cond.val = 0 ∨ cond.val = 1) :
    execProcedure env 2 s
      (Procedure.ofOps [Op.ifElse
        [Op.inst (.push 10), Op.inst .add]
        [Op.inst (.push 20), Op.inst .add]]) =
      some (if cond.val = 1
        then s.withStack ((x + 10) :: rest)
        else s.withStack ((x + 20) :: rest)) := by
  subst hs
  miden_vcg

-- ============================================================================
-- Test 5: ifElse via fast boolean-stack path
-- ============================================================================

/-- Validates the fast `miden_vcg` path for singleton ifElse when the stack
    condition is syntactically `if p then 1 else 0`. -/
theorem ifElse_bool_vcg_test
    (env : ProcEnv) (p : Prop) [Decidable p] (x : Felt)
    (rest : List Felt) :
    execProcedure env 2
      ⟨(if p then (1 : Felt) else 0) :: x :: rest, fun _ => 0, [], []⟩
      (Procedure.ofOps [Op.ifElse
        [Op.inst (.push 10), Op.inst .add]
        [Op.inst (.push 20), Op.inst .add]]) =
      some (if p
        then Concrete.State.withStack
          (⟨(if p then (1 : Felt) else 0) :: x :: rest, fun _ => 0, [], []⟩ : Concrete.State)
          ((x + 10) :: rest)
        else Concrete.State.withStack
          (⟨(if p then (1 : Felt) else 0) :: x :: rest, fun _ => 0, [], []⟩ : Concrete.State)
          ((x + 20) :: rest)) := by
  miden_vcg

/-- Validates the shallow `miden_vcg_step` split for boolean-encoded ifElse.
    The tactic should expose the two branch execution goals without recursive
    solving. -/
theorem ifElse_bool_vcg_step_test
    (env : ProcEnv) (p : Prop) [Decidable p] (x : Felt)
    (rest : List Felt) :
    execProcedure env 2
      ⟨(if p then (1 : Felt) else 0) :: x :: rest, fun _ => 0, [], []⟩
      (Procedure.ofOps [Op.ifElse
        [Op.inst (.push 10), Op.inst .add]
        [Op.inst (.push 20), Op.inst .add]]) =
      some (if p
        then Concrete.State.withStack
          (⟨(if p then (1 : Felt) else 0) :: x :: rest, fun _ => 0, [], []⟩ : Concrete.State)
          ((x + 10) :: rest)
        else Concrete.State.withStack
          (⟨(if p then (1 : Felt) else 0) :: x :: rest, fun _ => 0, [], []⟩ : Concrete.State)
          ((x + 20) :: rest)) := by
  miden_vcg_step
  · simp [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind,
      MidenLean.execInstruction, execPush, execAdd, Concrete.State.withStack]
  · simp [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind,
      MidenLean.execInstruction, execPush, execAdd, Concrete.State.withStack]

/-- Validates the fast `miden_vcg` path for singleton ifElse when the stack
    condition is syntactically `if p then 0 else 1`. -/
theorem ifElse_bool_neg_vcg_test
    (env : ProcEnv) (p : Prop) [Decidable p] (x : Felt)
    (rest : List Felt) :
    execProcedure env 2
      ⟨(if p then (0 : Felt) else 1) :: x :: rest, fun _ => 0, [], []⟩
      (Procedure.ofOps [Op.ifElse
        [Op.inst (.push 10), Op.inst .add]
        [Op.inst (.push 20), Op.inst .add]]) =
      some (if p
        then Concrete.State.withStack
          (⟨(if p then (0 : Felt) else 1) :: x :: rest, fun _ => 0, [], []⟩ : Concrete.State)
          ((x + 20) :: rest)
        else Concrete.State.withStack
          (⟨(if p then (0 : Felt) else 1) :: x :: rest, fun _ => 0, [], []⟩ : Concrete.State)
          ((x + 10) :: rest)) := by
  miden_vcg

-- ============================================================================
-- Test 6: whileTrue via miden_vcg — tactic applies execProcedure_while
-- ============================================================================

/-- While loop test: body = push 0, 1 iteration.
    Applies `execProcedure_while` directly with an explicit invariant and measure. -/
theorem while_vcg_test
    (env : ProcEnv) (fuel : Nat)
    (rest : List Felt) (mem : Nat → Felt)
    (frames : List LocalFrame) (adv : List Felt)
    (hfuel : fuel ≥ 2) :
    ∃ s', execProcedure.doWhile env fuel fuel
      [Op.inst (.push 0)]
      ⟨(1 : Felt) :: rest, mem, frames, adv⟩ = some s'
      ∧ s'.stack = rest := by
  have h1v : (1 : Felt).val = 1 :=
    felt_ofNat_val_lt 1 (by unfold GOLDILOCKS_PRIME; omega)
  have h0v : (0 : Felt).val = 0 :=
    felt_ofNat_val_lt 0 (by unfold GOLDILOCKS_PRIME; omega)
  -- Apply execProcedure_while directly with invariant and measure
  apply execProcedure_while
    (inv := fun s =>
      s = ⟨(1 : Felt) :: rest, mem, frames, adv⟩ ∨
      s = ⟨(0 : Felt) :: rest, mem, frames, adv⟩)
    (measure := fun s => match s.stack with | c :: _ => c.val | _ => 0)
  · -- hinit: invariant holds initially
    exact Or.inl rfl
  · -- hbool: top of stack is boolean
    intro s₀ hs₀
    rcases hs₀ with rfl | rfl
    · exact ⟨1, rest, rfl, Or.inr h1v⟩
    · exact ⟨0, rest, rfl, Or.inl h0v⟩
  · -- hstep: body preserves invariant, decreases measure
    intro s₀ cond_ rest₀ hs₀ hstk hcond
    rcases hs₀ with rfl | rfl
    · -- state = ⟨1 :: rest, ...⟩
      simp only [List.cons.injEq] at hstk; obtain ⟨rfl, rfl⟩ := hstk
      obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
      refine ⟨⟨(0 : Felt) :: rest, mem, frames, adv⟩, ?_, Or.inr rfl, ?_⟩
      · simp [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind,
              MidenLean.execInstruction, execPush, Concrete.State.withStack]
      · simp [h0v, h1v]
    · -- state = ⟨0 :: rest, ...⟩, cond.val = 1 → contradiction
      simp only [List.cons.injEq] at hstk; obtain ⟨rfl, rfl⟩ := hstk
      simp [h0v] at hcond
  · -- hexit: postcondition when cond = 0
    intro s₀ cond_ rest₀ hs₀ hstk hcond
    rcases hs₀ with rfl | rfl
    · simp only [List.cons.injEq] at hstk; obtain ⟨rfl, rfl⟩ := hstk
      simp [h1v] at hcond
    · simp only [List.cons.injEq] at hstk; obtain ⟨rfl, rfl⟩ := hstk
      simp [Concrete.State.withStack]
  · -- hfuel: fuel ≥ measure + 1
    simp [h1v]; omega

end MidenLean.ControlFlowTest
