import MidenLean.Proofs.StepLemmas

namespace MidenLean.Tactics

open MidenLean.StepLemmas

/-- Simplify one Option.bind step after a rewrite.
    Also normalizes List.set (from stepSwap), List.eraseIdx (from stepMovup),
    and insertAt/List.take/List.drop/List.append (from stepMovdn). -/
syntax "miden_bind" : tactic
macro_rules
  | `(tactic| miden_bind) =>
    `(tactic| simp only [bind, Bind.bind, Option.bind,
      List.set, List.eraseIdx, MidenLean.insertAt, List.take, List.drop,
      List.cons_append, List.nil_append, List.append_nil])

/-- Apply stepSwap with automatic argument resolution and normalize List.set. -/
syntax "miden_swap" : tactic
macro_rules
  | `(tactic| miden_swap) =>
    `(tactic|
      rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]; miden_bind)

/-- Apply stepDup with automatic index resolution. -/
syntax "miden_dup" : tactic
macro_rules
  | `(tactic| miden_dup) =>
    `(tactic| rw [stepDup (h := rfl)]; miden_bind)

/-- Apply stepMovup with automatic element resolution. -/
syntax "miden_movup" : tactic
macro_rules
  | `(tactic| miden_movup) =>
    `(tactic| rw [stepMovup (hn := rfl) (hv := rfl)]; miden_bind)

/-- Apply stepMovdn. -/
syntax "miden_movdn" : tactic
macro_rules
  | `(tactic| miden_movdn) =>
    `(tactic| rw [stepMovdn (hn := rfl)]; miden_bind)

/-- Try to apply a step lemma and simplify the bind.
    Covers all hypothesis-free step lemmas. For lemmas requiring hypotheses
    (stepU32And, stepU32Or, stepU32Xor, stepU32Assert2), use
    rw [stepU32And (ha := ...) (hb := ...)]; miden_bind manually. -/
syntax "miden_step" : tactic
macro_rules
  | `(tactic| miden_step) =>
    `(tactic| first
      | rw [stepDrop]; miden_bind
      | miden_dup
      | miden_swap
      | miden_movup
      | miden_movdn
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
      | rw [stepU32WidenMul]; miden_bind
      | rw [stepU32WidenMadd]; miden_bind
      | rw [stepU32Clz]; miden_bind
      | rw [stepU32Ctz]; miden_bind
      | rw [stepU32Clo]; miden_bind
      | rw [stepU32Cto]; miden_bind)

/-- Step through all remaining instructions, finishing with pure. -/
syntax "miden_steps" : tactic
macro_rules
  | `(tactic| miden_steps) =>
    `(tactic| repeat (first | miden_step | dsimp only [pure, Pure.pure]))

end MidenLean.Tactics
