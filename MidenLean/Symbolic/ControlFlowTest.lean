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
    ∃ s', execProcedure env 2
      ⟨cond :: x :: rest, mem, frames, adv⟩
      (Procedure.ofOps [Op.ifElse
        [Op.inst (.push 10), Op.inst .add]
        [Op.inst (.push 20), Op.inst .add]]) = some s' ∧
      ((cond.val = 1 → s'.stack = (x + 10) :: rest) ∧
       (cond.val = 0 → s'.stack = (x + 20) :: rest)) := by
  apply execProcedure_ifElse env 1 _ _ _ _ cond (x :: rest) rfl
  · intro h1
    refine ⟨⟨(x + 10) :: rest, mem, frames, adv⟩, ?_,
            fun _ => rfl, fun h0 => absurd h0 (by omega)⟩
    simp [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind,
          MidenLean.execInstruction, execPush, execAdd, Concrete.State.withStack]
  · intro h0
    refine ⟨⟨(x + 20) :: rest, mem, frames, adv⟩, ?_,
            fun h1 => absurd h1 (by omega), fun _ => rfl⟩
    simp [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind,
          MidenLean.execInstruction, execPush, execAdd, Concrete.State.withStack]
  · exact hbool

-- ============================================================================
-- Test 2: repeat with invariant — push 1 three times
-- ============================================================================

/-- Test execProcedure_repeat: repeat.3 { push 1 }.
    Input: [rest...], Output: [1, 1, 1, rest...] -/
theorem repeat_test
    (env : ProcEnv) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    ∃ s', execProcedure.doRepeat env 1 3 [Op.inst (.push 1)]
      ⟨rest, mem, frames, adv⟩ = some s'
      ∧ s'.stack = 1 :: 1 :: 1 :: rest := by
  obtain ⟨s', hexec, _, _, _, hs⟩ := execProcedure_repeat env 1 3 [Op.inst (.push 1)]
    ⟨rest, mem, frames, adv⟩
    (fun i s => s.memory = mem ∧ s.frames = frames ∧ s.advice = adv ∧
      s.stack = List.replicate i 1 ++ rest)
    ⟨rfl, rfl, rfl, rfl⟩
    (fun i s₀ _ ⟨hm, hf, ha, hs⟩ => by
      refine ⟨⟨1 :: s₀.stack, mem, frames, adv⟩, ?_, rfl, rfl, rfl, ?_⟩
      · simp [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind,
              MidenLean.execInstruction, execPush, Concrete.State.withStack, hm, hf, ha]
      · simp [hs, List.replicate_succ])
  exact ⟨s', hexec, hs⟩

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
    The tactic decomposes the control flow; branch proofs are manual. -/
theorem ifElse_vcg_test
    (env : ProcEnv) (cond x : Felt)
    (rest : List Felt) (mem : Nat → Felt)
    (frames : List LocalFrame) (adv : List Felt)
    (hbool : cond.val = 0 ∨ cond.val = 1) :
    ∃ s', execProcedure env 2
      ⟨cond :: x :: rest, mem, frames, adv⟩
      (Procedure.ofOps [Op.ifElse
        [Op.inst (.push 10), Op.inst .add]
        [Op.inst (.push 20), Op.inst .add]]) = some s' ∧
      ((cond.val = 1 → s'.stack = (x + 10) :: rest) ∧
       (cond.val = 0 → s'.stack = (x + 20) :: rest)) := by
  miden_vcg
  · -- then branch
    intro h1
    refine ⟨⟨(x + 10) :: rest, mem, frames, adv⟩, ?_,
            fun _ => rfl, fun h0 => absurd h0 (by omega)⟩
    simp [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind,
          MidenLean.execInstruction, execPush, execAdd, Concrete.State.withStack]
  · -- else branch
    intro h0
    refine ⟨⟨(x + 20) :: rest, mem, frames, adv⟩, ?_,
            fun h1 => absurd h1 (by omega), fun _ => rfl⟩
    simp [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind,
          MidenLean.execInstruction, execPush, execAdd, Concrete.State.withStack]
  · exact hbool

-- ============================================================================
-- Test 5: whileTrue via miden_vcg — tactic applies execProcedure_while
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
      simp at hstk; obtain ⟨rfl, rfl⟩ := hstk
      obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
      refine ⟨⟨(0 : Felt) :: rest, mem, frames, adv⟩, ?_, Or.inr rfl, ?_⟩
      · simp [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind,
              MidenLean.execInstruction, execPush, Concrete.State.withStack]
      · simp [h0v, h1v]
    · -- state = ⟨0 :: rest, ...⟩, cond.val = 1 → contradiction
      simp at hstk; obtain ⟨rfl, rfl⟩ := hstk
      simp [h0v] at hcond
  · -- hexit: postcondition when cond = 0
    intro s₀ cond_ rest₀ hs₀ hstk hcond
    rcases hs₀ with rfl | rfl
    · simp at hstk; obtain ⟨rfl, rfl⟩ := hstk
      simp [h1v] at hcond
    · simp at hstk; obtain ⟨rfl, rfl⟩ := hstk
      simp [Concrete.State.withStack]
  · -- hfuel: fuel ≥ measure + 1
    simp [h1v]; omega

end MidenLean.ControlFlowTest
