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

/-- If execution of the then-branch and else-branch both produce a state
    satisfying `P` (under the appropriate condition), then executing a
    singleton `ifElse` op succeeds and satisfies `P`. -/
theorem execWithEnv_ifElse
    (env : ProcEnv) (fuel : Nat)
    (thenOps elseOps : List Op) (s : MidenState)
    (P : MidenState → Prop)
    (cond : Felt) (rest : List Felt)
    (hs : s.stack = cond :: rest)
    (hthen : cond.val = 1 →
      ∃ s', execWithEnv env fuel (s.withStack rest) thenOps = some s' ∧ P s')
    (helse : cond.val = 0 →
      ∃ s', execWithEnv env fuel (s.withStack rest) elseOps = some s' ∧ P s')
    (hbool : cond.val = 0 ∨ cond.val = 1) :
    ∃ s', execWithEnv env (fuel + 1) s [Op.ifElse thenOps elseOps] = some s' ∧ P s' := by
  unfold execWithEnv
  simp only [Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind, pure, Pure.pure, hs]
  rcases hbool with h0 | h1
  · -- cond.val = 0: else branch
    obtain ⟨s', hexec, hp⟩ := helse h0
    exact ⟨s', by simp [h0, hexec], hp⟩
  · -- cond.val = 1: then branch
    obtain ⟨s', hexec, hp⟩ := hthen h1
    exact ⟨s', by simp [h1, hexec], hp⟩

-- repeat composition rule

/-- If an invariant holds initially and each iteration of the body preserves it,
    then after `n` iterations the invariant holds at index `n`.

    Direct induction on `n` with an explicit starting index. -/
theorem execWithEnv_repeat
    (env : ProcEnv) (fuel : Nat) (n : Nat) (body : List Op)
    (s : MidenState)
    (inv : Nat → MidenState → Prop)
    (hinit : inv 0 s)
    (hstep : ∀ i s₀, i < n → inv i s₀ →
      ∃ s₁, execWithEnv env fuel s₀ body = some s₁ ∧ inv (i + 1) s₁) :
    ∃ s', execWithEnv.doRepeat env fuel n body s = some s' ∧ inv n s' := by
  suffices ∀ k start s, start + k = n → inv start s →
      (∀ i s₀, start ≤ i → i < n → inv i s₀ →
        ∃ s₁, execWithEnv env fuel s₀ body = some s₁ ∧ inv (i + 1) s₁) →
      ∃ s', execWithEnv.doRepeat env fuel k body s = some s' ∧ inv n s' from
    this n 0 s (by omega) hinit (fun i s₀ _ hi hinv => hstep i s₀ hi hinv)
  intro k
  induction k with
  | zero =>
    intro start s hsk hinv _
    simp [execWithEnv.doRepeat]
    have : start = n := by omega
    subst this; exact hinv
  | succ k' ih =>
    intro start s hsk hinv hstep_bounded
    simp only [execWithEnv.doRepeat]
    obtain ⟨s₁, hexec, hinv₁⟩ := hstep_bounded start s le_rfl (by omega) hinv
    rw [hexec]
    exact ih (start + 1) s₁ (by omega) hinv₁
      (fun i s₀ hi₁ hi₂ hinv_i => hstep_bounded i s₀ (by omega) hi₂ hinv_i)

-- whileTrue composition rule

/-- If an invariant holds initially, the top of stack is always boolean under
    the invariant, and each continuation step preserves the invariant while
    decreasing a well-founded measure, then `doWhile` terminates and the
    postcondition holds on exit (when the condition is 0).

    The proof proceeds by induction on the loop-fuel parameter `f`, with
    the measure ensuring `f` is large enough for all iterations. -/
theorem execWithEnv_while
    (env : ProcEnv) (fuel : Nat)
    (body : List Op) (s : MidenState)
    (inv : MidenState → Prop)
    (post : MidenState → Prop)
    (measure : MidenState → Nat)
    (hinit : inv s)
    (hbool : ∀ s₀, inv s₀ →
      ∃ cond rest, s₀.stack = cond :: rest ∧ (cond.val = 0 ∨ cond.val = 1))
    (hstep : ∀ s₀ cond rest, inv s₀ →
      s₀.stack = cond :: rest →
      cond.val = 1 →
      ∃ s₁, execWithEnv env fuel (s₀.withStack rest) body = some s₁
             ∧ inv s₁ ∧ measure s₁ < measure s₀)
    (hexit : ∀ s₀ cond rest, inv s₀ →
      s₀.stack = cond :: rest →
      cond.val = 0 →
      post (s₀.withStack rest))
    (hfuel : fuel ≥ measure s + 1) :
    ∃ s', execWithEnv.doWhile env fuel fuel body s = some s' ∧ post s' := by
  suffices h : ∀ s₀ f, inv s₀ → measure s₀ < f → f ≤ fuel →
      ∃ s', execWithEnv.doWhile env fuel f body s₀ = some s' ∧ post s' from
    h s fuel hinit (by omega) le_rfl
  intro s₀ f hinv₀ hmeas hf_le
  induction f generalizing s₀ with
  | zero => omega
  | succ f' ih =>
    simp only [execWithEnv.doWhile]
    obtain ⟨cond, rest, hstk, hcond_bool⟩ := hbool s₀ hinv₀
    rw [hstk]
    rcases hcond_bool with h0 | h1
    · -- cond.val = 0: exit
      refine ⟨s₀.withStack rest, ?_, hexit s₀ cond rest hinv₀ hstk h0⟩
      simp [h0]
    · -- cond.val = 1: continue
      obtain ⟨s₁, hexec, hinv₁, hdec⟩ := hstep s₀ cond rest hinv₀ hstk h1
      have hexec' : execWithEnv env fuel (s₀.withStack rest) body = some s₁ :=
        execWithEnv_fuel_mono (by omega) hexec
      simp only [show (cond.val == 1) = true from by simp [h1], ite_true, hexec']
      exact ih s₁ hinv₁ (by omega) (by omega)

end MidenLean
