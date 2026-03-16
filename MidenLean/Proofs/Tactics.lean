import MidenLean.Proofs.StepLemmas

namespace MidenLean.Tactics

open MidenLean.StepLemmas

/-- Simplify one Option.bind step after a rewrite.
    Also normalizes List.set (produced by stepSwap). -/
syntax "miden_bind" : tactic
macro_rules
  | `(tactic| miden_bind) =>
    `(tactic| dsimp only [bind, Bind.bind, Option.bind, List.set])

/-- Try to apply a step lemma and simplify the bind.
    Falls back to trying each known step lemma.
    Note: Lemmas requiring hypotheses (stepU32And etc.) are excluded —
    use rw [stepU32And (ha := ...) (hb := ...)] manually for those. -/
syntax "miden_step" : tactic
macro_rules
  | `(tactic| miden_step) =>
    `(tactic| first
      | rw [stepDrop]; miden_bind
      | rw [stepDup (h := rfl)]; miden_bind
      | rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]; miden_bind
      | rw [stepMovup2]; miden_bind
      | rw [stepMovup3]; miden_bind
      | rw [stepMovdn2]; miden_bind
      | rw [stepMovdn3]; miden_bind
      | rw [stepEqImm]; miden_bind
      | rw [stepEq]; miden_bind
      | rw [stepNeq]; miden_bind
      | rw [stepAndIte]; miden_bind
      | rw [stepOrIte]; miden_bind
      | rw [stepNotIte]; miden_bind
      | rw [stepAddImm]; miden_bind
      | rw [stepU32WidenAdd]; miden_bind
      | rw [stepU32WidenAdd3]; miden_bind
      | rw [stepU32OverflowSub]; miden_bind
      | rw [stepU32Clz]; miden_bind
      | rw [stepU32Ctz]; miden_bind)

/-- Step through all remaining instructions, finishing with pure. -/
syntax "miden_steps" : tactic
macro_rules
  | `(tactic| miden_steps) =>
    `(tactic| repeat (first | miden_step | dsimp only [pure, Pure.pure]))

end MidenLean.Tactics
