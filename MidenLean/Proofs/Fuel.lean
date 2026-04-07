import MidenLean.Semantics

/-!
# Fuel monotonicity for `execWithEnv`

If execution succeeds with fuel `n`, it also succeeds (with the same result)
at any larger fuel `m ≥ n`.  The three mutually recursive functions
`execWithEnv`, `execWithEnv.doRepeat`, and `execWithEnv.doWhile` are handled
together via a bundled induction on the fuel parameter.
-/

namespace MidenLean

-- ============================================================================
-- Auxiliary: the per-op step function used inside execWithEnv's foldlM
-- ============================================================================

/-- The per-op step function that `execWithEnv` folds over the op list.
    Factored out so that fuel-monotonicity of the fold reduces to
    pointwise monotonicity of this function. -/
noncomputable def opStep (env : ProcEnv) (fuel : Nat)
    (state : MidenState) (op : Op) : Option MidenState :=
  match op with
  | Op.inst (Instruction.exec target) =>
    match env target with
    | some callee => execWithEnv env fuel state callee
    | none => none
  | Op.inst i => execInstruction state i
  | Op.ifElse thenBlk elseBlk =>
    match state.stack with
    | cond :: rest =>
      if (cond.val == 1) = true then
        execWithEnv env fuel (state.withStack rest) (Procedure.ofOps thenBlk)
      else if (cond.val == 0) = true then
        execWithEnv env fuel (state.withStack rest) (Procedure.ofOps elseBlk)
      else none
    | _ => none
  | Op.repeat count body =>
    execWithEnv.doRepeat env fuel count body state
  | Op.whileTrue body =>
    execWithEnv.doWhile env fuel fuel body state

-- ============================================================================
-- Unfold lemmas: execWithEnv at succ fuel reduces to foldlM of opStep
-- ============================================================================

private theorem execWithEnv_succ_zero (env : ProcEnv) (n : Nat)
    (s : MidenState) (name : String) (ops : List Op) :
    execWithEnv env (n + 1) s ⟨name, 0, ops⟩ =
    ops.foldlM (opStep env n) s := by
  unfold execWithEnv; rfl

private theorem execWithEnv_succ_locals (env : ProcEnv) (n : Nat)
    (s : MidenState) (name : String) (k : Nat) (ops : List Op) :
    execWithEnv env (n + 1) s ⟨name, k + 1, ops⟩ =
    let aligned := alignLocals (k + 1)
    let base := match s.frames with | [] => 0 | f :: _ => f.base + f.alignedNumLocals
    let frame : LocalFrame := { base, numLocals := k + 1, alignedNumLocals := aligned }
    let s' := { s with frames := frame :: s.frames }
    match ops.foldlM (opStep env n) s' with
    | some r => some { r with frames := s.frames }
    | none => none := by
  unfold execWithEnv; rfl

-- ============================================================================
-- Generic foldlM monotonicity for the Option monad
-- ============================================================================

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

-- ============================================================================
-- opStep pointwise monotonicity
-- ============================================================================

/-- If every sub-call (execWithEnv, doRepeat, doWhile) is fuel-monotonic at
    fuel `n`, then `opStep` is pointwise monotonic from fuel `n` to `m`. -/
private theorem opStep_fuel_mono (env : ProcEnv) (n m : Nat) (hm : n ≤ m)
    (s : MidenState) (op : Op) (s' : MidenState)
    (ihE : ∀ m s proc s', n ≤ m →
      execWithEnv env n s proc = some s' → execWithEnv env m s proc = some s')
    (ihR : ∀ m count body st st', n ≤ m →
      execWithEnv.doRepeat env n count body st = some st' →
      execWithEnv.doRepeat env m count body st = some st')
    (ihW : ∀ m fn fm body st st', n ≤ m → fn ≤ fm →
      execWithEnv.doWhile env n fn body st = some st' →
      execWithEnv.doWhile env m fm body st = some st')
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

-- ============================================================================
-- Main bundle: fuel monotonicity for all three functions simultaneously
-- ============================================================================

/-- Bundled fuel-monotonicity for `execWithEnv`, `doRepeat`, and `doWhile`.
    Proved by induction on the fuel parameter `n`. -/
private theorem fuel_mono_core (env : ProcEnv) :
    ∀ n : Nat,
    -- (E) execWithEnv is fuel-monotonic at fuel n
    (∀ m s proc s', n ≤ m →
      execWithEnv env n s proc = some s' →
      execWithEnv env m s proc = some s') ∧
    -- (R) doRepeat is fuel-monotonic at fuel n
    (∀ m count body st st', n ≤ m →
      execWithEnv.doRepeat env n count body st = some st' →
      execWithEnv.doRepeat env m count body st = some st') ∧
    -- (W) doWhile is fuel-monotonic at fuel n (both fuel and loop-fuel)
    (∀ m fn fm body st st', n ≤ m → fn ≤ fm →
      execWithEnv.doWhile env n fn body st = some st' →
      execWithEnv.doWhile env m fm body st = some st') := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    -- (E) execWithEnv at fuel 0 always returns none
    · intro m s proc s' _ h
      cases proc with | mk name numLocals ops => simp [execWithEnv] at h
    -- (R) doRepeat at fuel 0: only count = 0 succeeds (returning st unchanged)
    · intro m count body st st' _ h
      cases count with
      | zero =>
        simp only [execWithEnv.doRepeat] at h ⊢; exact h
      | succ k =>
        -- doRepeat calls execWithEnv at fuel 0, which is none
        simp only [execWithEnv.doRepeat] at h
        simp [execWithEnv] at h
    -- (W) doWhile at fuel 0
    · intro m fn fm body st st' _ hfn h
      cases fn with
      | zero => simp [execWithEnv.doWhile] at h
      | succ fn' =>
        simp only [execWithEnv.doWhile] at h
        split at h
        · next cond rest hstk =>
          split at h
          · -- cond = 1: calls execWithEnv at fuel 0, which is none
            simp [execWithEnv] at h
          · split at h
            · -- cond = 0: returns some (st.withStack rest)
              next h1 h2 =>
              obtain ⟨fm', rfl⟩ : ∃ fm', fm = fm' + 1 := ⟨fm - 1, by omega⟩
              simp only [execWithEnv.doWhile, hstk, h1, h2, ite_true] at h ⊢
              exact h
            · simp at h
        · simp at h
  | succ n ih =>
    obtain ⟨ihE, ihR, ihW⟩ := ih
    -- First prove (E) for fuel n+1, so we can use it in (R) and (W)
    have execE : ∀ m s proc s', n + 1 ≤ m →
        execWithEnv env (n + 1) s proc = some s' →
        execWithEnv env m s proc = some s' := by
      intro m s proc s' hm h
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hm' : n ≤ m' := by omega
      cases proc with | mk name numLocals ops =>
      cases numLocals with
      | zero =>
        rw [execWithEnv_succ_zero] at h ⊢
        exact foldlM_option_step_mono (opStep env n) (opStep env m') s ops
          (fun st op st' h => opStep_fuel_mono env n m' hm' st op st' ihE ihR ihW h) h
      | succ k =>
        rw [execWithEnv_succ_locals] at h ⊢
        simp only [] at h ⊢
        -- Name the framed initial state
        set s₀ := ({ s with
          frames := { base := match s.frames with | [] => 0 | f :: _ => f.base + f.alignedNumLocals
                      numLocals := k + 1
                      alignedNumLocals := alignLocals (k + 1) } :: s.frames
          } : MidenState) with hs₀
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
    -- ================================================================
    -- (R) doRepeat at fuel n + 1
    -- ================================================================
    · intro m count body st st' hm h
      induction count generalizing st with
      | zero =>
        simp only [execWithEnv.doRepeat] at h ⊢; exact h
      | succ k ihCount =>
        simp only [execWithEnv.doRepeat] at h ⊢
        split at h
        · next st'' heq =>
          have : execWithEnv env m st ↑body = some st'' := execE m st ↑body st'' hm heq
          simp [this]
          exact ihCount st'' h
        · simp at h
    -- ================================================================
    -- (W) doWhile at fuel n + 1
    -- ================================================================
    · intro m fn fm body st st' hm hfn h
      induction fn generalizing st fm with
      | zero => simp [execWithEnv.doWhile] at h
      | succ fn' ihFn =>
        obtain ⟨fm', rfl⟩ : ∃ fm', fm = fm' + 1 := ⟨fm - 1, by omega⟩
        have hfn' : fn' ≤ fm' := by omega
        -- Unfold doWhile at fn'+1 in h
        simp only [execWithEnv.doWhile] at h
        -- Case split on the stack in h
        split at h
        · next cond rest hstk =>
          -- Unfold doWhile at fm'+1 in the goal and rewrite the stack
          simp only [execWithEnv.doWhile, hstk]
          -- Case split on cond == 1
          split at h
          · next h1 =>
            -- cond = 1: calls execWithEnv, then doWhile recursively
            simp only [h1, ite_true]
            split at h
            · next st'' heq =>
              have hExec : execWithEnv env m (st.withStack rest) ↑body = some st'' :=
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

-- ============================================================================
-- Public API: individual monotonicity theorems
-- ============================================================================

/-- If `execWithEnv env n s proc = some s'` and `n ≤ m`, then
    `execWithEnv env m s proc = some s'`. -/
theorem execWithEnv_fuel_mono {env : ProcEnv} {n m : Nat} {s : MidenState}
    {proc : Procedure} {s' : MidenState} (hm : n ≤ m)
    (h : execWithEnv env n s proc = some s') :
    execWithEnv env m s proc = some s' :=
  (fuel_mono_core env n).1 m s proc s' hm h

/-- If `doRepeat env n count body st = some st'` and `n ≤ m`, then
    `doRepeat env m count body st = some st'`. -/
theorem doRepeat_fuel_mono {env : ProcEnv} {n m : Nat} {count : Nat}
    {body : List Op} {st st' : MidenState} (hm : n ≤ m)
    (h : execWithEnv.doRepeat env n count body st = some st') :
    execWithEnv.doRepeat env m count body st = some st' :=
  (fuel_mono_core env n).2.1 m count body st st' hm h

/-- If `doWhile env n fn body st = some st'` and `n ≤ m` and `fn ≤ fm`, then
    `doWhile env m fm body st = some st'`. -/
theorem doWhile_fuel_mono {env : ProcEnv} {n m : Nat} {fn fm : Nat}
    {body : List Op} {st st' : MidenState} (hm : n ≤ m) (hfn : fn ≤ fm)
    (h : execWithEnv.doWhile env n fn body st = some st') :
    execWithEnv.doWhile env m fm body st = some st' :=
  (fuel_mono_core env n).2.2 m fn fm body st st' hm hfn h

/-- Corollary: if execution succeeds at fuel `n`, it succeeds at fuel `n + k`
    with the same result. -/
theorem execWithEnv_fuel_mono_add {env : ProcEnv} {n : Nat} {s : MidenState}
    {proc : Procedure} {s' : MidenState} (k : Nat)
    (h : execWithEnv env n s proc = some s') :
    execWithEnv env (n + k) s proc = some s' :=
  execWithEnv_fuel_mono (Nat.le_add_right n k) h

end MidenLean
