import MidenLean.Symbolic.SimpAttrs
import MidenLean.Symbolic.Soundness
import MidenLean.Generated.U64

/-!
# Symbolic Reflection

End-to-end use of the symbolic block executor to prove correctness of
real MASM procedures. Two reflection theorems:
1. `reflect_with_env_zero` for procedures with numLocals = 0
2. `reflect_with_env_locals` for procedures with numLocals > 0
-/

namespace MidenLean.Symbolic.Reflect

open MidenLean
open MidenLean.Symbolic

/-- The concrete assignment used by tactic-facing reflection wrappers. -/
abbrev concreteAssignment : Assignment := fun _ => 0

/-- Concrete literal symbolic state matching a concrete stack prefix, memory,
    frames, and advice. -/
def concreteState (stackPrefix : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt) : State :=
  { stack := stackPrefix.map Expr.lit
    memory := fun addr => Expr.lit (mem addr)
    frames := frames
    advice := adv.map Expr.lit }

/-- Concrete literal symbolic state for the `numLocals > 0` reflection path.
    It pre-pushes the fresh local frame that `execWithEnv` would allocate. -/
def concreteStateWithLocals (stackPrefix : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (numLocals : Nat) : State :=
  let aligned := MidenLean.alignLocals numLocals
  let base := match frames with
    | [] => 0
    | f :: _ => f.base + f.alignedNumLocals
  let frame : MidenLean.LocalFrame := { base, numLocals, alignedNumLocals := aligned }
  { stack := stackPrefix.map Expr.lit
    memory := fun addr => Expr.lit (mem addr)
    frames := frame :: frames
    advice := adv.map Expr.lit }

private theorem map_eval_lit (xs : List Felt) :
    List.map ((Expr.eval (fun _ => 0)) ∘ Expr.lit) xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Expr.eval, ih]

@[simp, miden_reflect_norm] theorem map_eval_lit_concrete (xs : List Felt) :
    List.map (Expr.eval concreteAssignment) (xs.map Expr.lit) = xs := by
  simpa [concreteAssignment, Function.comp] using map_eval_lit xs

@[simp, miden_reflect_norm] theorem eval_concreteState_memory
    (stackPrefix : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt) (addr : Nat) :
    ((concreteState stackPrefix mem frames adv).memory addr).eval concreteAssignment = mem addr := by
  simp [concreteState, Expr.eval]

@[simp, miden_reflect_norm] theorem eval_concreteStateWithLocals_memory
    (stackPrefix : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (numLocals : Nat) (addr : Nat) :
    ((concreteStateWithLocals stackPrefix mem frames adv numLocals).memory addr).eval
        concreteAssignment = mem addr := by
  simp [concreteStateWithLocals, Expr.eval]

@[simp, miden_reflect_norm] theorem eval_if_concreteAssignment
    (c : Prop) [Decidable c] (t e : Expr) :
    Expr.eval concreteAssignment (if c then t else e) =
      if c then Expr.eval concreteAssignment t else Expr.eval concreteAssignment e := by
  by_cases h : c <;> simp [h]

@[simp, miden_reflect_norm] theorem eval_ite_zero_concrete (a b : Expr) :
    Expr.eval concreteAssignment (.ite (.lit 0) a b) = Expr.eval concreteAssignment b := by
  change (if (((0 : Felt).val == 1) = true) then Expr.eval concreteAssignment a
      else Expr.eval concreteAssignment b) = Expr.eval concreteAssignment b
  simp

@[simp, miden_reflect_norm] theorem eval_ite_one_concrete (a b : Expr) :
    Expr.eval concreteAssignment (.ite (.lit 1) a b) = Expr.eval concreteAssignment a := by
  change (if (((1 : Felt).val == 1) = true) then Expr.eval concreteAssignment a
      else Expr.eval concreteAssignment b) = Expr.eval concreteAssignment a
  have h : (((1 : Felt).val == 1) = true) = true := by native_decide
  simp [h]

@[simp] theorem concreteState_models
    (stackPrefix rest : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt) :
    (concreteState stackPrefix mem frames adv).models
      ⟨stackPrefix ++ rest, mem, frames, adv⟩ (fun _ => 0) rest := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · simpa [concreteState] using (congrArg (fun ys => ys ++ rest) (map_eval_lit stackPrefix)).symm
  · intro addr
    simp [concreteState, Expr.eval]
  · simpa [concreteState] using (map_eval_lit adv).symm

@[simp] theorem concreteStateWithLocals_models
    (stackPrefix rest : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (numLocals : Nat) :
    (concreteStateWithLocals stackPrefix mem frames adv numLocals).models
      (let aligned := MidenLean.alignLocals numLocals
       let base := match frames with
         | [] => 0
         | f :: _ => f.base + f.alignedNumLocals
       let frame : MidenLean.LocalFrame := { base, numLocals, alignedNumLocals := aligned }
       ⟨stackPrefix ++ rest, mem, frame :: frames, adv⟩) (fun _ => 0) rest := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · simpa [concreteStateWithLocals] using
      (congrArg (fun ys => ys ++ rest) (map_eval_lit stackPrefix)).symm
  · intro addr
    simp [concreteStateWithLocals, Expr.eval]
  · simpa [concreteStateWithLocals] using (map_eval_lit adv).symm

set_option linter.unusedVariables false in
/-- Reflection for procedures with numLocals = 0.
    Memory, frames, and advice pass through based on the symbolic execution result. -/
theorem reflect_with_env_zero
    (insts : List Instruction) (name : String) (ops : List MidenLean.Op)
    (env : MidenLean.ProcEnv) (fuel : Nat)
    (stack : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (n : Nat) (rest : List Felt)
    (σ : Assignment)
    (initSS : State)
    (result : BlockResult)
    (hops : ops = insts.map MidenLean.Op.inst)
    (hfuel : fuel > 0)
    (hnoexec : insts.all (fun i => !isExecInst i) = true)
    (hmodels : initSS.models ⟨stack, mem, frames, adv⟩ σ rest)
    (hresult : execBlock insts initSS = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds σ) :
    MidenLean.execWithEnv env fuel ⟨stack, mem, frames, adv⟩ ⟨name, 0, ops⟩ =
    some ⟨result.state.stack.map (Expr.eval σ) ++ rest,
          fun addr => (result.state.memory addr).eval σ,
          result.state.frames,
          result.state.advice.map (Expr.eval σ)⟩ := by
  rw [execWithEnv_basic_block_zero env fuel ⟨stack, mem, frames, adv⟩ insts name ops
      hops hfuel hnoexec]
  obtain ⟨cs', hconc, hmod⟩ :=
    execBlock_sound insts initSS ⟨stack, mem, frames, adv⟩ σ rest result
      hmodels hresult hpreconds
  rw [hconc]
  unfold State.models at hmod
  obtain ⟨hstk, hmem, hfr, hadv⟩ := hmod
  congr 1
  cases cs'
  simp only [MidenLean.MidenState.mk.injEq] at hstk hmem hfr hadv ⊢
  exact ⟨hstk, funext hmem, hfr, hadv⟩

set_option linter.unusedVariables false in
/-- Reflection for procedures with numLocals > 0.
    Frame is pushed before execution and popped after. -/
theorem reflect_with_env_locals
    (insts : List Instruction) (name : String) (k : Nat) (ops : List MidenLean.Op)
    (env : MidenLean.ProcEnv) (fuel : Nat)
    (stack : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (n : Nat) (rest : List Felt)
    (σ : Assignment)
    (initSS : State)
    (result : BlockResult)
    (hops : ops = insts.map MidenLean.Op.inst)
    (hfuel : fuel > 0)
    (hnoexec : insts.all (fun i => !isExecInst i) = true)
    (hmodels : initSS.models
      (let aligned := MidenLean.alignLocals (k + 1)
       let base := match frames with | [] => 0 | f :: _ => f.base + f.alignedNumLocals
       let frame : MidenLean.LocalFrame := { base, numLocals := k + 1, alignedNumLocals := aligned }
       ⟨stack, mem, frame :: frames, adv⟩) σ rest)
    (hresult : execBlock insts initSS = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds σ) :
    MidenLean.execWithEnv env fuel ⟨stack, mem, frames, adv⟩ ⟨name, k + 1, ops⟩ =
    some ⟨result.state.stack.map (Expr.eval σ) ++ rest,
          fun addr => (result.state.memory addr).eval σ,
          frames,
          result.state.advice.map (Expr.eval σ)⟩ := by
  cases frames with
  | nil =>
    rw [execWithEnv_basic_block_locals env fuel ⟨stack, mem, [], adv⟩ insts name k ops
        hops hfuel hnoexec]
    dsimp only []
    obtain ⟨cs', hconc, hmod⟩ :=
      execBlock_sound insts initSS _ σ rest result
        hmodels hresult hpreconds
    rw [hconc]
    unfold State.models at hmod
    obtain ⟨hstk, hmem, _, hadv⟩ := hmod
    cases cs' with | mk s m f a =>
    simp only [] at hstk hmem hadv ⊢
    subst hstk; subst hadv
    exact congrArg some (by congr 1; exact funext hmem)
  | cons f rest_frames =>
    rw [execWithEnv_basic_block_locals env fuel ⟨stack, mem, f :: rest_frames, adv⟩ insts name k ops
        hops hfuel hnoexec]
    dsimp only []
    obtain ⟨cs', hconc, hmod⟩ :=
      execBlock_sound insts initSS _ σ rest result
        hmodels hresult hpreconds
    rw [hconc]
    unfold State.models at hmod
    obtain ⟨hstk, hmem, _, hadv⟩ := hmod
    cases cs' with | mk s m fr a =>
    simp only [] at hstk hmem hadv ⊢
    subst hstk; subst hadv
    exact congrArg some (by congr 1; exact funext hmem)

/-- Tactic-facing zero-locals reflection wrapper for a fully concrete initial
    symbolic state. This hides the `State.models` setup proof. -/
theorem reflect_with_env_zero_concrete
    (insts : List Instruction) (name : String) (ops : List MidenLean.Op)
    (env : MidenLean.ProcEnv) (fuel : Nat)
    (stackPrefix rest : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (result : BlockResult)
    (hops : ops = insts.map MidenLean.Op.inst)
    (hfuel : fuel > 0)
    (hnoexec : insts.all (fun i => !isExecInst i) = true)
    (hresult : execBlock insts (concreteState stackPrefix mem frames adv) = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds (fun _ => 0)) :
    MidenLean.execWithEnv env fuel ⟨stackPrefix ++ rest, mem, frames, adv⟩ ⟨name, 0, ops⟩ =
    some ⟨result.state.stack.map (Expr.eval (fun _ => 0)) ++ rest,
          fun addr => (result.state.memory addr).eval (fun _ => 0),
          frames,
          result.state.advice.map (Expr.eval (fun _ => 0))⟩ := by
  have hmain :=
    reflect_with_env_zero insts name ops env fuel
      (stackPrefix ++ rest) mem frames adv
      stackPrefix.length rest
      (fun _ => 0)
      (concreteState stackPrefix mem frames adv)
      result
      hops hfuel hnoexec
      (concreteState_models stackPrefix rest mem frames adv)
      hresult hpreconds
  have hframes :
      result.state.frames = frames := by
    simpa [concreteState] using
      execBlock_preserves_frames insts (concreteState stackPrefix mem frames adv) result hresult
  simpa [hframes] using hmain

/-- Tactic-facing positive-locals reflection wrapper for a fully concrete
    initial symbolic state. This hides the `State.models` setup proof. -/
theorem reflect_with_env_locals_concrete
    (insts : List Instruction) (name : String) (k : Nat) (ops : List MidenLean.Op)
    (env : MidenLean.ProcEnv) (fuel : Nat)
    (stackPrefix rest : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (result : BlockResult)
    (hops : ops = insts.map MidenLean.Op.inst)
    (hfuel : fuel > 0)
    (hnoexec : insts.all (fun i => !isExecInst i) = true)
    (hresult : execBlock insts (concreteStateWithLocals stackPrefix mem frames adv (k + 1)) = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds (fun _ => 0)) :
    MidenLean.execWithEnv env fuel ⟨stackPrefix ++ rest, mem, frames, adv⟩ ⟨name, k + 1, ops⟩ =
    some ⟨result.state.stack.map (Expr.eval (fun _ => 0)) ++ rest,
          fun addr => (result.state.memory addr).eval (fun _ => 0),
          frames,
          result.state.advice.map (Expr.eval (fun _ => 0))⟩ := by
  simpa [concreteStateWithLocals] using
    reflect_with_env_locals insts name k ops env fuel
      (stackPrefix ++ rest) mem frames adv
      stackPrefix.length rest
      (fun _ => 0)
      (concreteStateWithLocals stackPrefix mem frames adv (k + 1))
      result
      hops hfuel hnoexec
      (concreteStateWithLocals_models stackPrefix rest mem frames adv (k + 1))
      hresult hpreconds

end MidenLean.Symbolic.Reflect
