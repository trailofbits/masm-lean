import MidenLean.Concrete.Exec

/-!
# Fuel monotonicity for `execProcedure`

If execution succeeds with fuel `n`, it also succeeds (with the same result)
at any larger fuel `m ≥ n`.  The three mutually recursive functions
`execProcedure`, `execProcedure.doRepeat`, and `execProcedure.doWhile` are handled
together via a bundled induction on the fuel parameter.
-/

namespace MidenLean

-- Auxiliary: the per-op step function used inside execProcedure's foldlM

/-- The per-op step function that `execProcedure` folds over the op list.
    Factored out so that fuel-monotonicity of the fold reduces to
    pointwise monotonicity of this function. -/
noncomputable def opStep (env : ProcEnv) (fuel : Nat)
    (state : Concrete.State) (op : Op) : Option Concrete.State :=
  match op with
  | Op.inst (Instruction.exec target) =>
    match env target with
    | some callee => execProcedure env fuel state callee
    | none => none
  | Op.inst i => execInstruction state i
  | Op.ifElse thenBlk elseBlk =>
    match state.stack with
    | cond :: rest =>
      if (cond.val == 1) = true then
        execProcedure env fuel (state.withStack rest) (Procedure.ofOps thenBlk)
      else if (cond.val == 0) = true then
        execProcedure env fuel (state.withStack rest) (Procedure.ofOps elseBlk)
      else none
    | _ => none
  | Op.repeat count body =>
    execProcedure.doRepeat env fuel count body state
  | Op.whileTrue body =>
    execProcedure.doWhile env fuel fuel body state

-- Unfold lemmas: execProcedure at succ fuel reduces to foldlM of opStep

theorem execProcedure_succ_zero (env : ProcEnv) (n : Nat)
    (s : Concrete.State) (name : String) (ops : List Op) :
    execProcedure env (n + 1) s ⟨name, 0, ops⟩ =
    ops.foldlM (opStep env n) s := by
  unfold execProcedure; rfl

theorem execProcedure_succ_locals (env : ProcEnv) (n : Nat)
    (s : Concrete.State) (name : String) (k : Nat) (ops : List Op) :
    execProcedure env (n + 1) s ⟨name, k + 1, ops⟩ =
    let aligned := alignLocals (k + 1)
    let base := match s.frames with | [] => 0 | f :: _ => f.base + f.alignedNumLocals
    let frame : LocalFrame := { base, numLocals := k + 1, alignedNumLocals := aligned }
    let s' := { s with frames := frame :: s.frames }
    match ops.foldlM (opStep env n) s' with
    | some r => some { r with frames := s.frames }
    | none => none := by
  unfold execProcedure; rfl

-- Generic foldlM monotonicity for the Option monad

private theorem foldlM_option_step_mono {α β : Type*}
    (f g : α → β → Option α) (init : α) (ops : List β)
    (h : ∀ s b s', f s b = some s' → g s b = some s')
    {fin : α} (hf : ops.foldlM f init = some fin) :
    ops.foldlM g init = some fin := by
  induction ops generalizing init with
  | nil => simpa using hf
  | cons op rest ih =>
    simp only [List.foldlM] at hf ⊢
    match hfop : f init op with
    | none => simp [hfop] at hf
    | some s' =>
      simp [hfop] at hf; simp [h init op s' hfop]
      exact ih s' hf

-- opStep pointwise monotonicity

/-- If every sub-call (execProcedure, doRepeat, doWhile) is fuel-monotonic at
    fuel `n`, then `opStep` is pointwise monotonic from fuel `n` to `m`. -/
private theorem opStep_fuel_mono (env : ProcEnv) (n m : Nat) (hm : n ≤ m)
    (s : Concrete.State) (op : Op) (s' : Concrete.State)
    (ihE : ∀ m s proc s', n ≤ m →
      execProcedure env n s proc = some s' → execProcedure env m s proc = some s')
    (ihR : ∀ m count body st st', n ≤ m →
      execProcedure.doRepeat env n count body st = some st' →
      execProcedure.doRepeat env m count body st = some st')
    (ihW : ∀ m fn fm body st st', n ≤ m → fn ≤ fm →
      execProcedure.doWhile env n fn body st = some st' →
      execProcedure.doWhile env m fm body st = some st')
    (h : opStep env n s op = some s') :
    opStep env m s op = some s' := by
  unfold opStep at h ⊢
  cases op with
  | inst i =>
    cases i with
    | exec target =>
      simp only [] at h ⊢
      split at h
      · exact ihE m s _ s' hm h
      · exact absurd h (by simp)
    | _ => exact h
  | ifElse thenBlk elseBlk =>
    cases hstk : s.stack with
    | nil => simp [hstk] at h
    | cons cond rest =>
      simp only [hstk] at h ⊢
      split
      · next h1 => simp [h1] at h; exact ihE m _ _ s' hm h
      · next h1 =>
        simp [h1] at h ⊢
        obtain ⟨hcond, h⟩ := h
        exact ⟨hcond, ihE m _ _ s' hm h⟩
  | «repeat» count body => exact ihR m count body s s' hm h
  | whileTrue body => exact ihW m n m body s s' hm hm h

-- Main bundle: fuel monotonicity for all three functions simultaneously

/-- Bundled fuel-monotonicity for `execProcedure`, `doRepeat`, and `doWhile`.
    Proved by induction on the fuel parameter `n`. -/
private theorem fuel_mono_core (env : ProcEnv) :
    ∀ n : Nat,
    -- (E) execProcedure is fuel-monotonic at fuel n
    (∀ m s proc s', n ≤ m →
      execProcedure env n s proc = some s' →
      execProcedure env m s proc = some s') ∧
    -- (R) doRepeat is fuel-monotonic at fuel n
    (∀ m count body st st', n ≤ m →
      execProcedure.doRepeat env n count body st = some st' →
      execProcedure.doRepeat env m count body st = some st') ∧
    -- (W) doWhile is fuel-monotonic at fuel n (both fuel and loop-fuel)
    (∀ m fn fm body st st', n ≤ m → fn ≤ fm →
      execProcedure.doWhile env n fn body st = some st' →
      execProcedure.doWhile env m fm body st = some st') := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    -- (E) execProcedure at fuel 0 always returns none
    · intro m s proc s' _ h
      cases proc with | mk name numLocals ops => simp [execProcedure] at h
    -- (R) doRepeat at fuel 0: only count = 0 succeeds (returning st unchanged)
    · intro m count body st st' _ h
      cases count with
      | zero =>
        simp only [execProcedure.doRepeat] at h ⊢; exact h
      | succ k =>
        -- doRepeat calls execProcedure at fuel 0, which is none
        simp only [execProcedure.doRepeat] at h
        simp [execProcedure] at h
    -- (W) doWhile at fuel 0
    · intro m fn fm body st st' _ hfn h
      cases fn with
      | zero => simp [execProcedure.doWhile] at h
      | succ fn' =>
        simp only [execProcedure.doWhile] at h
        split at h
        · next cond rest hstk =>
          split at h
          · -- cond = 1: calls execProcedure at fuel 0, which is none
            simp [execProcedure] at h
          · split at h
            · -- cond = 0: returns some (st.withStack rest)
              next h1 h2 =>
              obtain ⟨fm', rfl⟩ : ∃ fm', fm = fm' + 1 := ⟨fm - 1, by omega⟩
              simp only [execProcedure.doWhile, hstk, h1, h2, ite_true] at h ⊢
              exact h
            · simp at h
        · simp at h
  | succ n ih =>
    obtain ⟨ihE, ihR, ihW⟩ := ih
    -- First prove (E) for fuel n+1, so we can use it in (R) and (W)
    have execE : ∀ m s proc s', n + 1 ≤ m →
        execProcedure env (n + 1) s proc = some s' →
        execProcedure env m s proc = some s' := by
      intro m s proc s' hm h
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hm' : n ≤ m' := by omega
      cases proc with | mk name numLocals ops =>
      cases numLocals with
      | zero =>
        rw [execProcedure_succ_zero] at h ⊢
        exact foldlM_option_step_mono (opStep env n) (opStep env m') s ops
          (fun st op st' h => opStep_fuel_mono env n m' hm' st op st' ihE ihR ihW h) h
      | succ k =>
        rw [execProcedure_succ_locals] at h ⊢
        simp only [] at h ⊢
        -- Name the framed initial state
        set s₀ := ({ s with
          frames := { base := match s.frames with | [] => 0 | f :: _ => f.base + f.alignedNumLocals
                      numLocals := k + 1
                      alignedNumLocals := alignLocals (k + 1) } :: s.frames
          } : Concrete.State) with hs₀
        -- Extract foldlM result from h
        match hres : List.foldlM (opStep env n) s₀ ops with
        | some r =>
          rw [hres] at h
          simp only [Option.some.injEq] at h
          have hmono := foldlM_option_step_mono (opStep env n) (opStep env m') s₀ ops
            (fun st op st' h => opStep_fuel_mono env n m' hm' st op st' ihE ihR ihW h)
            hres
          rw [hmono]
          simp only [Option.some.injEq]
          exact h
        | none =>
          rw [hres] at h
          simp at h
    refine ⟨execE, ?_, ?_⟩
    -- (R) doRepeat at fuel n + 1
    · intro m count body st st' hm h
      induction count generalizing st with
      | zero =>
        simp only [execProcedure.doRepeat] at h ⊢; exact h
      | succ k ihCount =>
        simp only [execProcedure.doRepeat] at h ⊢
        split at h
        · next st'' heq =>
          have : execProcedure env m st ↑body = some st'' := execE m st ↑body st'' hm heq
          simp [this]
          exact ihCount st'' h
        · simp at h
    -- (W) doWhile at fuel n + 1
    · intro m fn fm body st st' hm hfn h
      induction fn generalizing st fm with
      | zero => simp [execProcedure.doWhile] at h
      | succ fn' ihFn =>
        obtain ⟨fm', rfl⟩ : ∃ fm', fm = fm' + 1 := ⟨fm - 1, by omega⟩
        have hfn' : fn' ≤ fm' := by omega
        -- Unfold doWhile at fn'+1 in h
        simp only [execProcedure.doWhile] at h
        -- Case split on the stack in h
        split at h
        · next cond rest hstk =>
          -- Unfold doWhile at fm'+1 in the goal and rewrite the stack
          simp only [execProcedure.doWhile, hstk]
          -- Case split on cond == 1
          split at h
          · next h1 =>
            -- cond = 1: calls execProcedure, then doWhile recursively
            simp only [h1, ite_true]
            split at h
            · next st'' heq =>
              have hExec : execProcedure env m (st.withStack rest) ↑body = some st'' :=
                execE m (st.withStack rest) ↑body st'' hm heq
              rw [hExec]
              exact ihFn fm' st'' hfn' h
            · simp at h
          · split at h
            · next h1 h2 =>
              -- cond = 0: returns some (st.withStack rest)
              simp only [h1, h2, ite_true]
              exact h
            · simp at h
        · simp at h

-- Public API: individual monotonicity theorems

/-- If `execProcedure env n s proc = some s'` and `n ≤ m`, then
    `execProcedure env m s proc = some s'`. -/
theorem execProcedure_fuel_mono {env : ProcEnv} {n m : Nat} {s : Concrete.State}
    {proc : Procedure} {s' : Concrete.State} (hm : n ≤ m)
    (h : execProcedure env n s proc = some s') :
    execProcedure env m s proc = some s' :=
  (fuel_mono_core env n).1 m s proc s' hm h

end MidenLean
