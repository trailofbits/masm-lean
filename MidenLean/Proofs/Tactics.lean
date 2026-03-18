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
    Covers hypothesis-free step lemmas and u32 step lemmas whose isU32
    hypotheses can be resolved by `assumption`. For lemmas requiring
    hypotheses not in the context (stepU32And, stepU32Or, stepU32Xor,
    stepU32Assert2), use manual invocation. -/
syntax "miden_step" : tactic
macro_rules
  | `(tactic| miden_step) =>
    `(tactic| first
      | rw [stepDrop]; miden_bind
      | rw [stepReversew]; miden_bind
      | rw [stepDropw]; miden_bind
      | rw [stepPush]; miden_bind
      | rw [stepAdd]; miden_bind
      | rw [stepMul]; miden_bind
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
      | rw [stepU32Split]; miden_bind
      | rw [stepLt]; miden_bind
      | rw [stepGt]; miden_bind
      | (rw [stepPow2 (ha := by omega)]; miden_bind)
      | (rw [stepU32WrappingSub (ha := by assumption) (hb := by assumption)]; miden_bind)
      | (rw [stepU32Lt (ha := by assumption) (hb := by assumption)]; miden_bind)
      | (rw [stepU32DivMod (ha := by assumption) (hb := by assumption) (hbz := by omega)]; miden_bind)
      | (rw [stepU32WidenAdd (ha := by assumption) (hb := by assumption)]; miden_bind)
      | (rw [stepU32WidenAdd3 (ha := by assumption) (hb := by assumption) (hc := by assumption)]; miden_bind)
      | (rw [stepU32OverflowSub (ha := by assumption) (hb := by assumption)]; miden_bind)
      | (rw [stepU32WidenMul (ha := by assumption) (hb := by assumption)]; miden_bind)
      | (rw [stepU32WidenMadd (ha := by assumption) (hb := by assumption) (hc := by assumption)]; miden_bind)
      | (rw [stepU32Clz (ha := by assumption)]; miden_bind)
      | (rw [stepU32Ctz (ha := by assumption)]; miden_bind)
      | (rw [stepU32Clo (ha := by assumption)]; miden_bind)
      | (rw [stepU32Cto (ha := by assumption)]; miden_bind)
      | (rw [stepDupw (h0 := rfl) (h1 := rfl) (h2 := rfl) (h3 := rfl)]; miden_bind)
      | (rw [stepDiv (hb := by assumption)]; miden_bind)
      | (rw [stepCdropIte]; miden_bind)
      | (rw [stepCswapIte]; miden_bind))

/-- Step through all remaining instructions, finishing with pure. -/
syntax "miden_steps" : tactic
macro_rules
  | `(tactic| miden_steps) =>
    `(tactic| repeat (first | miden_step | dsimp only [pure, Pure.pure]))

set_option hygiene false in
syntax "miden_setup" ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| miden_setup $proc) =>
    `(tactic|
      obtain ⟨stk, mem, locs, adv⟩ := s;
      simp only [MidenState.withStack] at hs ⊢;
      subst hs;
      unfold $proc exec execWithEnv;
      simp only [List.foldlM];
      try dsimp only [bind, Bind.bind, Option.bind])

set_option hygiene false in
syntax "miden_setup_env" ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| miden_setup_env $proc) =>
    `(tactic|
      obtain ⟨stk, mem, locs, adv⟩ := s;
      simp only [MidenState.withStack] at hs ⊢;
      subst hs;
      unfold $proc execWithEnv;
      simp only [List.foldlM];
      try dsimp only [bind, Bind.bind, Option.bind])

set_option hygiene false in
syntax "miden_call" ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| miden_call $proc) =>
    `(tactic|
      dsimp only [bind, Bind.bind, Option.bind];
      unfold $proc execWithEnv;
      simp only [List.foldlM, bind, Bind.bind, Option.bind, pure, Pure.pure])

end MidenLean.Tactics
