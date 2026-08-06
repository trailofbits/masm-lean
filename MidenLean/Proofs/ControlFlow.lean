import MidenLean.Proofs.Helpers
import MidenLean.Proofs.Fuel

/-!
# Control Flow Composition Rules

Composition rules for `ifElse`, `repeat`, and `whileTrue` that let proofs
reason about control flow without unfolding the concrete interpreter.
Each rule delegates straight-line segments to the caller (typically
`miden_reflect`).
-/

namespace MidenLean

-- ifElse composition rule

/-- Equality-oriented singleton `ifElse` rule. Each branch may produce a
    different output state; the result is
    `if cond.val = 1 then s_then else s_else`.
    When both branches produce the same state, the `if` simplifies away.
    Used by `miden_vcg` for ifElse decomposition. -/
theorem execProcedure_ifElse
    (env : ProcEnv) (fuel : Nat)
    (thenOps elseOps : List Op) (s : Concrete.State)
    (s_then s_else : Concrete.State)
    (cond : Felt) (rest : List Felt)
    (hs : s.stack = cond :: rest)
    (hfuel : fuel > 0)
    (hthen : cond.val = 1 →
      execProcedure env (fuel - 1) (s.withStack rest) thenOps = some s_then)
    (helse : cond.val = 0 →
      execProcedure env (fuel - 1) (s.withStack rest) elseOps = some s_else)
    (hbool : cond.val = 0 ∨ cond.val = 1) :
    execProcedure env fuel s [Op.ifElse thenOps elseOps] =
      some (if cond.val = 1 then s_then else s_else) := by
  cases fuel with
  | zero => omega
  | succ fuel' =>
      simp only [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind, pure,
        Pure.pure, hs]
      rcases hbool with h0 | h1
      · have helse' : execProcedure env fuel' (s.withStack rest) elseOps = some s_else := by
          simpa using helse h0
        simp [h0, helse']
      · have hthen' : execProcedure env fuel' (s.withStack rest) thenOps = some s_then := by
          simpa using hthen h1
        simp [h1, hthen']

/-- Same-output specialization of `execProcedure_ifElse`. When both branches
    produce the same state `s'`, the `if` collapses and the result is `some s'`.
    Used by `miden_vcg` when the goal RHS is a single state. -/
theorem execProcedure_ifElse_same
    (env : ProcEnv) (fuel : Nat)
    (thenOps elseOps : List Op) (s s' : Concrete.State)
    (cond : Felt) (rest : List Felt)
    (hs : s.stack = cond :: rest)
    (hfuel : fuel > 0)
    (hthen : cond.val = 1 →
      execProcedure env (fuel - 1) (s.withStack rest) thenOps = some s')
    (helse : cond.val = 0 →
      execProcedure env (fuel - 1) (s.withStack rest) elseOps = some s')
    (hbool : cond.val = 0 ∨ cond.val = 1) :
    execProcedure env fuel s [Op.ifElse thenOps elseOps] = some s' := by
  have h := execProcedure_ifElse env fuel thenOps elseOps s s' s' cond rest hs hfuel hthen helse hbool
  simp only [ite_self] at h; exact h

-- repeat composition rules

/-- Singleton `repeat 0` is the identity. -/
theorem execProcedure_repeat_zero
    (env : ProcEnv) (fuel : Nat) (body : List Op) (s : Concrete.State)
    (hfuel : fuel > 0) :
    execProcedure env fuel s [Op.repeat 0 body] = some s := by
  cases fuel with
  | zero => omega
  | succ fuel' =>
      simp [execProcedure, Procedure.ofOps, execProcedure.doRepeat]

/-- Singleton `repeat (n + 1)` peels off one iteration: execute the body,
    then execute `repeat n` on the resulting state.
    Used by `miden_vcg` for repeat decomposition. -/
theorem execProcedure_repeat_succ
    (env : ProcEnv) (fuel n : Nat) (body : List Op)
    (s s₁ s' : Concrete.State)
    (hfuel : fuel > 0)
    (hbody : execProcedure env (fuel - 1) s body = some s₁)
    (hrest : execProcedure env fuel s₁ [Op.repeat n body] = some s') :
    execProcedure env fuel s [Op.repeat (n + 1) body] = some s' := by
  cases fuel with
  | zero => omega
  | succ fuel' =>
      have hbody' : execProcedure env fuel' s body = some s₁ := by
        simpa using hbody
      have hrest' : execProcedure.doRepeat env fuel' n body s₁ = some s' := by
        simpa [execProcedure, Procedure.ofOps] using hrest
      simp [execProcedure, Procedure.ofOps, execProcedure.doRepeat, hbody', hrest']

-- whileTrue composition rule

/-- If an invariant holds initially, the top of stack is always boolean under
    the invariant, and each continuation step preserves the invariant while
    decreasing a well-founded measure, then `doWhile` terminates and the
    postcondition holds on exit (when the condition is 0).

    The proof proceeds by induction on the loop-fuel parameter `f`, with
    the measure ensuring `f` is large enough for all iterations. -/
theorem execProcedure_while
    (env : ProcEnv) (fuel : Nat)
    (body : List Op) (s : Concrete.State)
    (inv : Concrete.State → Prop)
    (post : Concrete.State → Prop)
    (measure : Concrete.State → Nat)
    (hinit : inv s)
    (hbool : ∀ s₀, inv s₀ →
      ∃ cond rest, s₀.stack = cond :: rest ∧ (cond.val = 0 ∨ cond.val = 1))
    (hstep : ∀ s₀ cond rest, inv s₀ →
      s₀.stack = cond :: rest →
      cond.val = 1 →
      ∃ s₁, execProcedure env fuel (s₀.withStack rest) body = some s₁
             ∧ inv s₁ ∧ measure s₁ < measure s₀)
    (hexit : ∀ s₀ cond rest, inv s₀ →
      s₀.stack = cond :: rest →
      cond.val = 0 →
      post (s₀.withStack rest))
    (hfuel : fuel ≥ measure s + 1) :
    ∃ s', execProcedure.doWhile env fuel fuel body s = some s' ∧ post s' := by
  suffices h : ∀ s₀ f, inv s₀ → measure s₀ < f → f ≤ fuel →
      ∃ s', execProcedure.doWhile env fuel f body s₀ = some s' ∧ post s' from
    h s fuel hinit (by omega) le_rfl
  intro s₀ f hinv₀ hmeas hf_le
  induction f generalizing s₀ with
  | zero => omega
  | succ f' ih =>
    simp only [execProcedure.doWhile]
    obtain ⟨cond, rest, hstk, hcond_bool⟩ := hbool s₀ hinv₀
    rw [hstk]
    rcases hcond_bool with h0 | h1
    · -- cond.val = 0: exit
      refine ⟨s₀.withStack rest, ?_, hexit s₀ cond rest hinv₀ hstk h0⟩
      simp [h0]
    · -- cond.val = 1: continue
      obtain ⟨s₁, hexec, hinv₁, hdec⟩ := hstep s₀ cond rest hinv₀ hstk h1
      have hexec' : execProcedure env fuel (s₀.withStack rest) body = some s₁ :=
        execProcedure_fuel_mono (by omega) hexec
      simp only [show (cond.val == 1) = true from by simp [h1], ite_true, hexec']
      exact ih s₁ hinv₁ (by omega) (by omega)

end MidenLean
